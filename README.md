rsfs
====

[![Build Status](https://travis-ci.org/twmb/rsfs.svg?branch=master)](https://travis-ci.org/twmb/rsfs)  [![Crates.io](https://img.shields.io/crates/v/rsfs.svg)](https://crates.io/crates/rsfs)


This crate provides a generic filesystem with implementations for normal
(disk), in memory, and test work sets.

This crate is particularly useful when your code interacts with disk and
attempts to recover from potential disk errors. It is difficult to trigger disk
errors in testing, meaning that generally you have to code around your
interactions with disk and then test these edges. That can lead to real, unknown
problems at runtime when disk problems occur in ways you did not expect.

With this crate, you can inject errors in a predictable manner while testing,
and you can operate with disk normally while running in production.

Not all platforms are supported, but I welcome changes that add more support.

See the crate [documentation](https://docs.rs/rsfs/) for a longer explanation
on usage and examples of usage.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
rsfs = "0.1"
```

and this to your crate root:

```rust
extern crate rsfs;
```
