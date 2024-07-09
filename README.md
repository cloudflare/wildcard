[![Build Status](https://github.com/cloudflare/wildcard/workflows/CI/badge.svg)](https://github.com/cloudflare/wildcard/actions?query=workflow%3ACI)
[![Dependency status](https://deps.rs/repo/github/cloudflare/wildcard/status.svg)](https://deps.rs/repo/github/cloudflare/wildcard)
[![crates.io](https://img.shields.io/crates/v/wildcard.svg)](https://crates.io/crates/wildcard)
[![Downloads](https://img.shields.io/crates/d/wildcard.svg)](https://crates.io/crates/wildcard)
[![Github stars](https://img.shields.io/github/stars/cloudflare/wildcard.svg?logo=github)](https://github.com/cloudflare/wildcard/stargazers)
[![Documentation](https://docs.rs/wildcard/badge.svg)](https://docs.rs/wildcard/)
[![License](https://img.shields.io/crates/l/wildcard.svg)](./LICENSE)

# `wildcard`

<!-- cargo-rdme start -->

`wildcard` is a rust crate for wildcard matching.

Here's how to use it:

```rust
let wildcard = Wildcard::new("*foo?*bar".as_bytes()).unwrap();

assert!(wildcard.is_match("fooofooobar".as_bytes()));
```

Special characters can be escaped to represent their literal symbol:

```rust
let wildcard = Wildcard::new(r"\*\?".as_bytes()).unwrap();

assert!(!wildcard.is_match("ab".as_bytes()));
assert!(wildcard.is_match("*?".as_bytes()));
```

You can also capture the substring that matched the metasymbols of the wildcard:

```rust
let wildcard = Wildcard::new("* is a * style?".as_bytes()).unwrap();

let captures: Vec<&[u8]> = wildcard.captures("Lambic is a beer style!".as_bytes()).unwrap();

assert_eq!(captures, ["Lambic".as_bytes(), "beer".as_bytes(), "!".as_bytes()]);
```

## Matching customization

With `wildcard` you can configure these properties of a wildcard:

1. Configure the symbols for the metasymbols `*` and `?` as well as the escape symbol.
2. Support for the metasymbol `?` can be disabled.
3. Support for escaping can be disabled.
4. Support for case-insensitive matching.

<!-- cargo-rdme end -->
