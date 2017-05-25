//! An in-memory filesystem that allows error injection.
//!
//! The [`FS`] provides an in-memory file system that allows injecting errors. This module is built
//! on top of the [`mem`] module provided by this crate; read that module documentation first to
//! understand how the in-memory aspects of this filesystem will behave.
//!
//! Injected errors are consumed via a FIFO queue. The calling API passes a sequence of closures
//! that will be passed which function a filesystem call is in if the function can error. The
//! sequence of closures is drained as they return `Some(Result)`; if a closure returns `None`, the
//! closure is not drained from the sequence.
//!
#[cfg(unix)]
#[path = "unix.rs"]
mod fs;

pub use self::fs::*;

mod unix;

// TODO redo this documentation when eventually making this module public.
