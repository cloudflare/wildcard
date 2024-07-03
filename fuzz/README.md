# Fuzzing `wildcard`

To fuzz wildcard you first need to install [`cargo-fuzz`](https://crates.io/crates/cargo-fuzz). To do so run
`cargo install cargo-fuzz`.

You can then run any of the fuzz targets (such as `fuzz_is_match` and `fuzz_captures`):

```shell
cargo +nightly fuzz run <fuzz-target> 
```
