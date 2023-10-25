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

const TVMASM_BIN_NAME = "tvmasm";

export async function activate(context: ExtensionContext) {
  const traceOutputChannel = window.createOutputChannel(
    "TVM Assembler Server Trace"
  );
  traceOutputChannel.appendLine("TVM Assembler Server Trace");

  const serverPathEnv = process.env["TVMASM_PATH"];
  const serverPathConfig = workspace
    .getConfiguration("tvmasm")
    .get<string>("languageServerPath");
  const defaultPath = getFromPath(
    TVMASM_BIN_NAME,
    path.join(os.homedir(), "bin", TVMASM_BIN_NAME)
  );
  const serverPath = serverPathConfig || serverPathEnv || defaultPath;
  if (!fs.existsSync(serverPath)) {
    window.showErrorMessage(`TVM Assembler binary not found at ${serverPath}`);
    process.exit(1);
  }

  const run: Executable = {
    command: serverPath,
    args: ["lsp"],
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
      "tvmasm-lsp",
      "Language client extension for TVM Assembler",
      serverOptions,
      clientOptions
    );
  };

  let disposable = commands.registerCommand(
    "tvmasm.restartLanguageServer",
    async () => {
      await deactivate();
      client = makeClient();
      await client.start();

      window.showInformationMessage("Reloaded TVM language Server");
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
