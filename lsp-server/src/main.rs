use tower_lsp::{LspService, Server};

use self::backend::Backend;

mod backend;
mod util;

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let env_filter = tracing_subscriber::EnvFilter::from_default_env();

    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_writer(|| {
            let tmp_dir = std::env::temp_dir();
            let log_file_path = tmp_dir.join("tvm-lsp-server.log");
            std::io::BufWriter::new(
                std::fs::OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(log_file_path)
                    .expect("Failed to open tvm-lsp-server.log"),
            )
        })
        .with_env_filter(env_filter)
        .finish();

    tracing::subscriber::set_global_default(subscriber).unwrap();

    let (service, socket) = LspService::new(|client| Backend::new(client));
    Server::new(stdin, stdout, socket).serve(service).await;
}
