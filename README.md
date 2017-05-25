rsfs
====

[![Build Status](https://travis-ci.org/twmb/rsfs.svg?branch=master)](https://travis-ci.org/twmb/rsfs)  [![Crates.io](https://img.shields.io/crates/v/rsfs.svg)](https://crates.io/crates/rsfs) [![Documentation](https://docs.rs/rsfs/badge.svg)](https://docs.rs/rsfs/badge.svg)


This crate provides a generic filesystem with disk and in-memory
implementations.

In the future, a module will be provided that will allow injecting errors into
filesystem operations in your tests on an in-memory filesystem. This _used_ to
exist but was removed in commit 1ee34f6.

This crate is currently particularly useful becacuse it provides a solid
in-memory filesystem. In the future, it will be _more_ useful for triggering
filesystem errors in your unit tests to enable testing of how your code handles
filesystem errors.

See the crate [documentation](https://docs.rs/rsfs/) for a longer explanation
on usage and examples of usage.
