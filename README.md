# everscale-asm &emsp; [![crates-io-batch]][crates-io-link] [![docs-badge]][docs-url] [![rust-version-badge]][rust-version-link] [![workflow-badge]][workflow-link]

[crates-io-batch]: https://img.shields.io/crates/v/everscale-asm.svg

[crates-io-link]: https://crates.io/crates/everscale-asm

[docs-badge]: https://docs.rs/everscale-asm/badge.svg

[docs-url]: https://docs.rs/everscale-asm

[rust-version-badge]: https://img.shields.io/badge/rustc-1.70+-lightgray.svg

[rust-version-link]: https://blog.rust-lang.org/2023/06/01/Rust-1.70.0.html

[workflow-badge]: https://img.shields.io/github/actions/workflow/status/broxus/everscale-asm/master.yaml?branch=master

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

### Building a contract using CLI
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

## Syntax

```
// Single-line comments

// Opcodes must be in uppercase, can start with a digit or minus,
// and can contain '#' or '_'
NOP
2DROP
-ROT
STREF_L

// Opcodes with number as an argument
PUSHINT 12
PUSHINT -0xded
PUSHINT 0b10110101

// Opcodes with stack register as an argument
PUSH s1
XCHG s10, s100
PU2XC s1, s(-1), s(-2)

// Opcodes with control registers (c0, .., c5, c7)
PUSH c3
PUSHCTR c7

// Opcodes with slice or continuation
PUSHSLICE x{123123_}
PUSHSLICE b{10001001}
IFREFELSEREF {
  PUSHINT 1
}, {
  PUSHINT 2
}
```

[Full opcodes list](https://test.ton.org/tvm.pdf)

## Contributing

We welcome contributions to the project! If you notice any issues or errors, feel free to open an issue or submit a pull request.

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.
