# everscale-asm &emsp; [![crates-io-batch]][crates-io-link] [![docs-badge]][docs-url] [![rust-version-badge]][rust-version-link] [![workflow-badge]][workflow-link]

[crates-io-batch]: https://img.shields.io/crates/v/everscale-asm.svg

[crates-io-link]: https://crates.io/crates/everscale-asm

[docs-badge]: https://docs.rs/everscale-asm/badge.svg

[docs-url]: https://docs.rs/everscale-asm

[rust-version-badge]: https://img.shields.io/badge/rustc-1.70+-lightgray.svg

[rust-version-link]: https://blog.rust-lang.org/2023/06/01/Rust-1.70.0.html

[workflow-badge]: https://img.shields.io/github/actions/workflow/status/broxus/everscale-asm/master.yml?branch=master

[workflow-link]: https://github.com/broxus/everscale-asm/actions?query=workflow%3Amaster

> Status: WIP

## About

Rust implementation of TVM Assembler.

## LSP Server/Client

- Install [TVM Assembler](https://marketplace.visualstudio.com/items?itemName=Rexagon.tvmasm-lsp) VSCode extension
- Install CLI
  ```bash
  cargo install --locked tvmasm
  ```

## How to use

### Build a contract using CLI
```bash
tvmasm build ./src/tests/walletv3.tvm -o walletv3.boc
```
Output:
```
Code path:      walletv3.boc
Code hash:      84dafa449f98a6987789ba232358072bc0f76dc4524002a5d0918b9a75d2d599
Unique cells:   1
Unique bits:    888
```

### Building a contract from Rust
```rust
use everscale_asm::Code;
use everscale_types::prelude::Cell;

let code: Cell = Code::assemble(r#"
    PUSHINT 1
    SWAP DUP
    PUSHCONT {
        TUCK
        MUL
        SWAP
        DEC
    }
    REPEAT
    DROP
"#)?;
```

## Contributing

We welcome contributions to the project! If you notice any issues or errors, feel free to open an issue or submit a pull request.

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.
