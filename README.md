rsfs
====

[![Build Status](https://travis-ci.org/twmb/rsfs.svg?branch=master)](https://travis-ci.org/twmb/rsfs)  [![Crates.io](https://img.shields.io/crates/v/rsfs.svg)](https://crates.io/crates/rsfs) [![Documentation](https://docs.rs/rsfs/badge.svg)](https://docs.rs/rsfs/badge.svg)


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

## Help Requested

The entire design of this crate revolves around Unix systems. I would love help
making everything cross system portable, but I do not know the internals of how
other systems need to work so much.

Additionally, even inside Unix, the errors I am using are the most Unix-system
common error codes. There are some platforms that use slightly different error
numbers. This would be an easy fix, as the `libc` crate has error codes for all
systems.

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
