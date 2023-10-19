import { ExtensionContext, window, workspace, commands } from "vscode";
import {
  Executable,
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
} from "vscode-languageclient/node";
import * as path from "path";
import * as fs from "fs";
import * as os from "os";

let client: LanguageClient;

const getFromPath = (bin: string, def: string) => {
  const paths = process.env["PATH"]?.split(path.delimiter) || [];
  const binPaths = paths.map((x) => path.join(x, bin));
  const found = binPaths.find((x) => {
    return fs.existsSync(x);
  });
  return found || def;
};

const TVM_LSP_SERVER_BIN_NAME = "tvm-lsp-server";

export async function activate(context: ExtensionContext) {
  const traceOutputChannel = window.createOutputChannel(
    "TVM Language Server Trace"
  );
  traceOutputChannel.appendLine("TVM Language Server Trace");

  const serverPathEnv = process.env["TVM_LSP_SERVER_PATH"];
  const serverPathConfig = workspace
    .getConfiguration("tvm")
    .get<string>("languageServerPath");
  const defaultPath = getFromPath(
    TVM_LSP_SERVER_BIN_NAME,
    path.join(os.homedir(), "bin", TVM_LSP_SERVER_BIN_NAME)
  );
  const serverPath = serverPathConfig || serverPathEnv || defaultPath;
  if (!fs.existsSync(serverPath)) {
    window.showErrorMessage(`TVM Language Server not found at ${serverPath}`);
    process.exit(1);
  }

  const run: Executable = {
    command: serverPath,
    options: {
      env: {
        ...process.env,
        RUST_LOG: "debug",
      },
    },
  };
  const serverOptions: ServerOptions = {
    run,
    debug: run,
  };

  const clientOptions: LanguageClientOptions = {
    documentSelector: [
      {
        scheme: "file",
        language: "tvm",
      },
    ],
    outputChannel: traceOutputChannel,
    traceOutputChannel,
  };

  const makeClient = () => {
    return new LanguageClient(
      "tvm-lsp",
      "Language client extension for TVM language server",
      serverOptions,
      clientOptions
    );
  };

  let disposable = commands.registerCommand(
    "tvm.restartLanguageServer",
    async () => {
      await deactivate();
      client = makeClient();
      await client.start();

      window.showInformationMessage("Reloaded TVM Language Server");
    }
  );

  client = makeClient();
  client.start();

  context.subscriptions.push(disposable);
}

export function deactivate(): Thenable<void> | undefined {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
