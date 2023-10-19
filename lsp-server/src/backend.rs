use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use async_trait::async_trait;
use tokio::sync::mpsc;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer};

use crate::util::*;

pub struct Backend {
    client: Client,
    state: Arc<BackendState>,
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self {
            client: client.clone(),
            state: Arc::new(BackendState::new(client)),
        }
    }

    async fn add_file(&self, path: &Url, text: String) {
        self.state
            .documents
            .insert(path.to_string(), Source::new(text));

        self.on_file_change(FileAction::Open, path).await;
    }

    async fn remove_file(&self, path: &Url) {
        self.state.documents.remove(path.as_str());
        self.on_file_change(FileAction::Close, path).await;
    }

    async fn update_file(&self, path: &Url, text: String) {
        self.state
            .documents
            .insert(path.to_string(), Source::new(text));

        self.on_file_change(FileAction::Update, path).await;
    }

    fn update_file_range(&self, _path: &Url, _range: Range, _text: String) {
        unimplemented!("update_file_range")
    }

    async fn on_file_change(&self, action: FileAction, path: &Url) {
        if action == FileAction::Update {
            self.state.document_diagnostics.remove(path.as_str());
        }

        if let Err(e) = self
            .state
            .queue_job(Job::ComputeDiagnostics(path.clone()))
            .await
        {
            tracing::error!("failed to queue job: {e:?}");
        }
    }
}

#[async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        let state = self.state.clone();
        tokio::spawn(async move { state.process_jobs().await });

        Ok(InitializeResult {
            server_info: None,
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Options(
                    TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(TextDocumentSyncKind::FULL),
                        ..Default::default()
                    },
                )),
                // completion_provider: Some(CompletionOptions {
                //     resolve_provider: Some(true),
                //     ..Default::default()
                // }),
                document_highlight_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "server initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    #[tracing::instrument(skip_all)]
    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let file_path = params.text_document.uri;
        tracing::debug!(
            %file_path,
            lang_id = params.text_document.language_id,
            "did_open request"
        );

        let text = params.text_document.text;
        self.client
            .log_message(
                MessageType::INFO,
                format!("did_open request for {file_path}"),
            )
            .await;
        self.add_file(&file_path, text).await;
    }

    #[tracing::instrument(skip_all)]
    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let file_path = params.text_document.uri;
        tracing::debug!(%file_path, "did_change request");

        for content_change in params.content_changes {
            match content_change.range {
                Some(range) => self.update_file_range(&file_path, range, content_change.text),
                None => self.update_file(&file_path, content_change.text).await,
            }
        }

        self.client
            .log_message(
                MessageType::INFO,
                format!("did_change request for {file_path}"),
            )
            .await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        let file_path = params.text_document.uri;
        tracing::debug!(%file_path, "did_close request");
        self.client
            .log_message(
                MessageType::INFO,
                format!("did_close request for {file_path}"),
            )
            .await;
        self.remove_file(&file_path).await;
    }
}

struct BackendState {
    client: Client,
    documents: FastDashMap<String, Source>,
    document_diagnostics: FastDashMap<String, Vec<Diagnostic>>,
    jobs_sender: mpsc::Sender<Job>,
    jobs_receiver: tokio::sync::RwLock<mpsc::Receiver<Job>>,
    progress_id: AtomicU64,
}

impl BackendState {
    fn new(client: Client) -> Self {
        let (jobs_sender, jobs_receiver) = mpsc::channel::<Job>(100);

        Self {
            client,
            documents: Default::default(),
            document_diagnostics: Default::default(),
            jobs_sender,
            jobs_receiver: tokio::sync::RwLock::new(jobs_receiver),
            progress_id: AtomicU64::new(0),
        }
    }

    async fn process_jobs(&self) {
        use tower_lsp::lsp_types::notification::Progress;
        use tower_lsp::lsp_types::request::WorkDoneProgressCreate;

        let mut receiver = self.jobs_receiver.write().await;
        while let Some(job) = receiver.recv().await {
            tracing::debug!(?job, "processing job");
            match job {
                Job::ComputeDiagnostics(_path) => {
                    let req_token = ProgressToken::Number(
                        self.progress_id.fetch_add(1, Ordering::Release) as i32,
                    );

                    let create_req = self
                        .client
                        .send_request::<WorkDoneProgressCreate>(WorkDoneProgressCreateParams {
                            token: req_token.clone(),
                        })
                        .await;

                    if create_req.is_ok() {
                        self.client
                            .send_notification::<Progress>(ProgressParams {
                                token: req_token.clone(),
                                value: ProgressParamsValue::WorkDone(WorkDoneProgress::Begin(
                                    WorkDoneProgressBegin {
                                        title: "Processing".to_owned(),
                                        ..Default::default()
                                    },
                                )),
                            })
                            .await;
                    }

                    // TODO: process

                    if create_req.is_ok() {
                        self.client
                            .send_notification::<Progress>(ProgressParams {
                                token: req_token,
                                value: ProgressParamsValue::WorkDone(WorkDoneProgress::End(
                                    WorkDoneProgressEnd {
                                        message: Some("Processing finished".to_owned()),
                                    },
                                )),
                            })
                            .await;
                    }
                }
            }
        }
    }

    #[tracing::instrument(skip_all)]
    async fn queue_job(&self, job: Job) -> anyhow::Result<()> {
        tracing::debug!(?job, "queueing job");

        let sender = self.jobs_sender.clone();
        Ok(sender.send(job).await?)
    }
}

pub struct Source {
    pub text: String,
    pub line_lengths: Vec<usize>,
}

impl Source {
    pub fn new(text: String) -> Self {
        let line_lengths = text.as_str().lines().map(|x| x.len()).collect();
        Self { text, line_lengths }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum FileAction {
    Open,
    Close,
    Update,
}

#[derive(Debug)]
pub enum Job {
    ComputeDiagnostics(Url),
}
