//! Convenience functions and types for working with [`std::path::Path`].
//!
//! This module deliberately ignores Window's prefixes for now, but I would welcome a change that
//! adds it.
//!
//! [`std::path::Path`]: https://doc.rust-lang.org/std/path/struct.Path.html

use std::ffi::OsString;
use std::path::{Component, Path, PathBuf};

/// An iterator with `peek()` and `peek2()` calls that return optional references to the next
/// element or the one after.
///
/// This struct is created by the [`peek2able()`] extension method on [`Iterator`] provided by this
/// module's [`IteratorExt`].
///
/// [`peek2able()`]: trait.IteratorExt.html#method.peek2able
/// [`Iterator`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html
/// [`IteratorExt`]: trait.IteratorExt.html
#[derive(Debug)]
pub struct Peek2able<I: Iterator> {
    // iter is the original iterator that we now have a Peek2able of.
    iter: I,
    // peek1 is the stashed value corresponding to the first lookahead from a peek or peek2 call,
    // or the second value from a peek2 call after next has been called once.
    peek1: Option<Option<I::Item>>,
    // peek2 is the stashed value corresponding to the second lookahead from a `.peek2()` call.
    peek2: Option<Option<I::Item>>,
}

/// An extension to add two-element lookahead to an iterator.
pub trait IteratorExt<I: Iterator> {
    /// Creates an iterator that can look at he next two elments from the iterator without
    /// consuming it.
    ///
    /// Adds [`peek()`] and [`peek2()`] methods to an iterator.
    ///
    /// Note that the underlying iterator is still advanced when either [`peek()`] or [`peek2()`]
    /// is called for the first time. In order to peek, [`next()`] is called, hence any side
    /// effects of the [`next()`] method will occur.
    ///
    /// [`next()`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#tymethod.next
    /// [`peek()`]: struct.Peek2able.html#method.peek
    /// [`peek2()`]: struct.Peek2able.html#method.peek2
    fn peek2able(self) -> Peek2able<I>;
}

impl<I: Iterator> IteratorExt<I> for I {
    fn peek2able(self) -> Peek2able<I> {
        Peek2able {
            iter: self,
            peek1: None,
            peek2: None,
        }
    }
}

impl<I: Iterator> Iterator for Peek2able<I> {
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        match self.peek1.take() {
            Some(v) => {
                self.peek1 = self.peek2.take();
                v
            }
            None => self.iter.next(),
        }
    }
}

impl<I: Iterator> Peek2able<I> {
    /// Returns a reference to the next `.next()` value without advancing the iterator.
    #[allow(dead_code)]
    pub fn peek(&mut self) -> Option<&I::Item> {
        if self.peek1.is_none() {
            self.peek1 = Some(self.iter.next());
        }
        match self.peek1 {
            Some(Some(ref value)) => Some(value),
            Some(None) => None,
            _ => unreachable!(),
        }
    }
    pub fn peek2(&mut self) -> Option<&I::Item> {
        if self.peek1.is_none() {
            self.peek1 = Some(self.iter.next());
        }
        if self.peek2.is_none() {
            self.peek2 = Some(self.iter.next());
        }
        match self.peek2 {
            Some(Some(ref value)) => Some(value),
            Some(None) => None,
            _ => unreachable!(),
        }
    }
}

/// A simplified version of [`std::path::Component`].
///
/// [`std::path::Component`]: https://doc.rust-lang.org/std/path/enum.Component.html
#[derive(Clone, Debug, PartialEq)]
pub enum Part {
    /// A `..` in a path that could not be normalized away.
    ParentDir,
    /// A file or directory name.
    Normal(OsString),
}

impl Part {
    /// Borrows a `Normal` path part's `OsString` path.
    pub fn as_normal(&self) -> Option<&OsString> {
        match *self {
            Part::Normal(ref s) => Some(s),
            Part::ParentDir => None,
        }
    }
    /// Consumes a `Normal` path part into its `OsString` path.
    pub fn into_normal(self) -> Option<OsString> {
        match self {
            Part::Normal(s) => Some(s),
            Part::ParentDir => None,
        }
    }
}

/// Wraps information about a path and provides iterators over the components in that path.
///
/// This struct is created by the [`normalize`] function.
///
/// [`normalize`]: fn.normalize.html
#[derive(Debug)]
pub struct Parts {
    // at_root signifies whether the original path, normalized, began at root.
    pub at_root: bool,
    // inner contains all normal inner of a path and, if not at root, may begin with a few
    // parent directories.
    pub inner: Vec<Part>,
}

impl Default for Parts {
    fn default() -> Parts {
        Parts { at_root: false, inner: vec![] }
    }
}

impl From<Part> for Parts {
    fn from(p: Part) -> Parts {
        Parts { at_root: false, inner: vec![p] }
    }
}

impl From<Parts> for PathBuf {
    fn from(ps: Parts) -> PathBuf {
        let mut b = PathBuf::new();
        for p in ps.inner {
            match p {
                Part::ParentDir => b.push(".."),
                Part::Normal(n) => b.push(n),
            }
        }
        b
    }
}

/// Returns the shortest [`Parts`] equivalent to path purely by lexical parsing.
///
/// - replaces multiple path separators with one
/// - eliminates each `.`
/// - replaces `..` with the non `..` that preceeds it
///
/// Effectively, this is [`std::fs::canonicalize`] except for this operates on a potential path.
///
/// [`Parts`]: struct.Parts.html
/// [`std::fs::canonicalize`]: https://doc.rust-lang.org/std/fs/fn.canonicalize.html
pub fn normalize<P: AsRef<Path>>(path: &P) -> Parts {
    let mut ps = Parts {
        at_root: false,
        inner: Vec::new(),
    };
    for comp in path.as_ref().components() {
        match comp {
            Component::RootDir => ps.at_root = true,
            Component::ParentDir => {
                if ps.at_root || ps.inner.last().map_or(false, |last| *last != Part::ParentDir) {
                    ps.inner.pop();
                } else {
                    ps.inner.push(Part::ParentDir);
                }
            }
            Component::Normal(p) => {
                ps.inner.push(Part::Normal(p.to_os_string()));
            }
            _ => (),
        }
    }
    ps
}
