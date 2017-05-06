//! An in memory filesystem that allows error injection.
//!
//! The [`FS`] provides an in memory file system that allows injecting errors. This module is built
//! on top of the [`mem`] module provided by this crate; read that module documentation first to
//! understand how the in memory aspects of this filesystem will behave.
//!
//! Injected errors are consumed via a FIFO queue. The calling API passes a sequence of closures
//! that will be passed which function a filesystem call is in if the function can error. The
//! sequence of closures is drained as they return `Some(Result)`; if a closure returns `None`, the
//! closure is not drained from the sequence.
//!

// # Example
//
// ```
// use rsfs::*;
// use rsfs::errors::*;
// use rsfs::unix_ext::*;
// use rsfs::mem::test::fs::{FS, In, AtFile};
// use std::io::{Read, Result, Seek, SeekFrom, Write};
//
// let fs = FS::with_mode(0o300);
//
//
// // open a file, write some content...
// let mut wf =
//     fs.new_openopts().mode(0o600).write(true).create_new(true).open("f").unwrap();
// assert_eq!(wf.write(vec![0, 1, 2, 3, 4, 5].as_slice()).unwrap(), 6);
//
// // open the file for reading...
// let mut rf = fs.new_openopts().read(true).open("f").unwrap();
//
// // read some content, consuming the first closure in the sequence...
// let mut output = [0u8; 4];
// assert_eq!(rf.read(&mut output).unwrap(), 4);
// assert_eq!(&output, &[0, 1, 2, 3]);
//
// // notice that other file operations will not fail
// assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);
//
// // consume the second closure, which will error...
// assert!(rf.read(&mut output).is_err());
//
// // now we are back to normal and that same read will be successful...
// assert_eq!(rf.read(&mut output).unwrap(), 4);
// assert_eq!(&output, &[1, 2, 3, 4]);
// ```
//
// [`FS`]: struct.FS.html
// [`mem`]: ../mem/index.html
//

extern crate parking_lot;

use std::cmp;
use std::ffi::OsString;
use std::io::{Read, Result, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use self::parking_lot::Mutex;

use fs;
use mem::fs as mem;
use unix_ext;

/// The `testfs` is about to call a [`DirBuilder`] method.
///
/// [`DirBuilder`]: ../fs/trait.DirBuilder.html
pub enum AtDirBuilder<'inj: 'p, 'p> {
    /// The next call will be [`create`].
    ///
    /// [`create`]: ../fs/trait.DirBuilder.html#tymethod.create
    Create(&'p DirBuilder<'inj>, &'p PathBuf),
}

/// The `testfs` is about to call a [`DirEntry`] method.
///
/// [`DirEntry`]: ../fs/trait.DirEntry.html
pub enum AtDirEntry<'inj: 'p, 'p> {
    /// The next call will be [`metadata`].
    ///
    /// [`metadata`]: ../fs/trait.DirEntry.html#tymethod.metadata
    Metadata(&'p DirEntry<'inj>),
    /// The next call will be [`file_type`].
    ///
    /// [`file_type`]: ../fs/trait.DirEntry.html#tymethod.file_type
    FileType(&'p DirEntry<'inj>),
}

/// The `testfs` is about to call a [`File`] method.
///
/// [`File`]: ../fs/trait.File.html
pub enum AtFile<'inj: 'p, 'p> {
    /// The next call will be [`metadata`].
    ///
    /// [`metadata`]: ../fs/trait.File.html#tymethod.metadata
    Metadata(&'p File<'inj>),
    /// The next call will be [`flush`].
    ///
    /// [`flush`]: https://doc.rust-lang.org/std/io/trait.Write.html#tymethod.flush
    Flush(&'p File<'inj>),
    /// The next call will be [`seek`].
    ///
    /// [`seek`]: https://doc.rust-lang.org/std/io/trait.Seek.html#tymethod.seek
    Seek(&'p File<'inj>, &'p SeekFrom),
}

pub enum AtFilePartial<'inj: 'p, 'p> {
    Read(&'p File<'inj>, &'p [u8]),
    Write(&'p File<'inj>, &'p [u8]),
}

/// The `testfs` is about to call an [`OpenOptions`] method.
///
/// [`OpenOptions`]: ../fs/trait.OpenOptions.html
pub enum AtOpenOptions<'inj: 'p, 'p> {
    /// The next call will be [`open`].
    ///
    /// [`open`]: ../fs/trait.OpenOptions.html#tymethod.open
    Open(&'p OpenOptions<'inj>, &'p PathBuf),
}

/// The `testfs` is about to call a [`ReadDir`] method.
///
/// [`ReadDir`]: ../fs/trait.ReadDir.html
pub enum AtReadDir<'inj: 'p, 'p> {
    /// The next call will be [`next`].
    ///
    /// [`next`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html#tymethod.next
    Next(&'p ReadDir<'inj>),
}

/// The `testfs` is about to call an [`FS`] method.
///
/// [`FS`]: ../fs/trait.FS.html
pub enum AtFS<'p> {
    /// The next call will be [`metadata`].
    ///
    /// [`metadata`]: ../fs/trait.FS.html#tymethod.metadata
    Metadata(&'p PathBuf),
    /// The next call will be [`read_dir`].
    ///
    /// [`read_dir`]: ../fs/trait.FS.html#tymethod.read_dir
    ReadDir(&'p PathBuf),
    /// The next call will be [`remove_dir`].
    ///
    /// [`remove_dir`]: ../fs/trait.FS.html#tymethod.remove_dir
    RemoveDir(&'p PathBuf),
    /// The next call will be [`remove_dir_all`].
    ///
    /// [`remove_dir_all`]: ../fs/trait.FS.html#tymethod.remove_dir_all
    RemoveDirAll(&'p PathBuf),
    /// The next call will be [`remove_file`].
    ///
    /// [`remove_file`]: ../fs/trait.FS.html#tymethod.remove_file
    RemoveFile(&'p PathBuf),
    /// The next call will be [`rename`].
    ///
    /// [`rename`]: ../fs/trait.FS.html#tymethod.rename
    Rename(&'p PathBuf, &'p PathBuf),
    /// The next call will be [`set_permissions`].
    ///
    /// [`set_permissions`]: ../fs/trait.FS.html#tymethod.set_permissions
    SetPermissions(&'p PathBuf, &'p mem::Permissions),
}

/// The `testfs` is about to call a method that can error.
pub enum In<'inj: 'p, 'p> {
    /// The `testfs` is about to call a [`DirBuilder`] method. See the [`AtDirBuilder`]
    /// enum.
    ///
    /// [`DirBuilder`]: ../fs/trait.DirBuilder.html
    /// [`AtDirBuilder`]: enum.AtDirBuilder.html
    DirBuilder(AtDirBuilder<'inj, 'p>),
    /// The `testfs` is about to call a [`DirEntry`] method. See the [`AtDirEntry`] enum.
    ///
    /// [`DirEntry`]: ../fs/trait.DirEntry.html
    /// [`AtDirEntry`]: enum.AtDirEntry.html
    DirEntry(AtDirEntry<'inj, 'p>),
    /// The `testfs` is about to call a [`File`] method. See the [`AtFile`] enum.
    ///
    /// [`File`]: ../fs/trait.File.html
    /// [`AtFile`]: enum.AtFile.html
    File(AtFile<'inj, 'p>),
    /// The `testfs` is about to call an [`OpenOptions`] method. See the
    /// [`AtOpenOptions`] enum.
    ///
    /// [`OpenOptions`]: ../fs/trait.OpenOptions.html
    /// [`AtOpenOptions`]: enum.AtOpenOptions.html
    OpenOptions(AtOpenOptions<'inj, 'p>),
    /// The `testfs` is about to call a [`ReadDir`] method. See the [`AtReadDir`] enum.
    ///
    /// [`ReadDir`]: ../fs/trait.ReadDir.html
    /// [`AtReadDir`]: enum.AtReadDir.html
    ReadDir(AtReadDir<'inj, 'p>),
    /// The `testfs` is about to call an [`FS`] method. See the [`AtFS`] enum.
    ///
    /// [`FS`]: ../fs/trait.FS.html
    /// [`AtFS`]: enum.AtFS.html
    FS(AtFS<'p>),
}

/// A builder used to create directories in various manners.
///
/// This struct wraps [`mem::DirBuilder`] with the addition that `.create()` can potentially
/// consume a [`testfs`] injected error. See the module [documentation] for an example.
///
/// [`mem::DirBuilder`]: ../mem/struct.DirBuilder.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct DirBuilder<'inj> {
    injector: InjectFn<'inj>,
    pub inner: mem::DirBuilder,
}

impl<'inj> fs::DirBuilder for DirBuilder<'inj> {
    fn recursive(&mut self, recursive: bool) -> &mut Self {
        self.inner.recursive(recursive);
        self
    }
    fn create<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) = injector
               .as_mut()
               .map(|f| {
                        f(In::DirBuilder(AtDirBuilder::Create(self, &path.as_ref().to_owned())))
                    }) {
            r?;
        }
        self.inner.create(path)
    }
}

impl<'inj> unix_ext::DirBuilderExt for DirBuilder<'inj> {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.inner.mode(mode);
        self
    }
}

/// Entries returned by the [`ReadDir`] iterator.
///
/// This struct wraps [`mem::DirEntry`] with the addition that `.metadata()` can potentially
/// consume a [`testfs`] injected error. See the module [documentation] for an example.
///
/// [`ReadDir`]: struct.ReadDir.html
/// [`mem::DirEntry`]: ../mem/struct.DirEntry.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct DirEntry<'inj> {
    injector: InjectFn<'inj>,
    pub inner: mem::DirEntry,
}

impl<'inj> fs::DirEntry for DirEntry<'inj> {
    type Metadata = mem::Metadata;
    type FileType = mem::FileType;

    fn path(&self) -> PathBuf {
        self.inner.path()
    }
    fn metadata(&self) -> Result<Self::Metadata> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(In::DirEntry(AtDirEntry::Metadata(self)))) {
            r?;
        }
        self.inner.metadata()
    }
    fn file_type(&self) -> Result<Self::FileType> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(In::DirEntry(AtDirEntry::FileType(self)))) {
            r?;
        }
        self.inner.file_type()
    }
    fn file_name(&self) -> OsString {
        self.inner.file_name()
    }
}

/// A view into a file on the filesystem.
///
/// This struct wraps [`mem::File`] with the addition that file methods can potentially consume
/// [`testfs`] injected errors. See the module [documentation] for an example.
///
/// [`mem::File`]: ../mem/struct.File.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct File<'inj> {
    injector: InjectFn<'inj>,
    file_injector: InjectFilePartialFn<'inj>,
    inner: mem::File,
}

impl<'inj> fs::File for File<'inj> {
    type Metadata = mem::Metadata;

    fn metadata(&self) -> Result<Self::Metadata> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(In::File(AtFile::Metadata(self)))) {
            r?;
        }
        self.inner.metadata()
    }
}

impl<'inj> Read for File<'inj> {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let mut injector = self.file_injector.lock(); // always hold for the entire fn
        // The injector may return Ok, but that we should read a small number of bytes.
        let mut sz = buf.len();
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(AtFilePartial::Read(self, buf))) {
            sz = cmp::min(r?, buf.len());
        }
        self.inner.read(&mut buf[..sz])
    }
}

impl<'inj> Write for File<'inj> {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        let mut injector = self.file_injector.lock(); // always hold for the entire fn
        // The injector may return Ok, but that we should write a small number of bytes.
        let mut sz = buf.len();
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(AtFilePartial::Write(self, buf))) {
            sz = cmp::min(r?, buf.len());
        }
        self.inner.write(&buf[..sz])
    }
    fn flush(&mut self) -> Result<()> {
        self.inner.flush()
    }
}

impl<'inj> Seek for File<'inj> {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(In::File(AtFile::Seek(self, &pos)))) {
            r?;
        }
        self.inner.seek(pos)
    }
}

/// Options and flags which can be used to configure how a file is opened.
///
/// This struct wraps [`mem::OpenOptions`] with the addition that `.open()` can potentially consume
/// a [`testfs`] injected error. See the module [documentation] for an example.
///
/// [`mem::OpenOptions`]: ../mem/struct.OpenOptions.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct OpenOptions<'inj> {
    injector: InjectFn<'inj>,
    file_injector: InjectFilePartialFn<'inj>,
    inner: mem::OpenOptions,
}

impl<'inj> fs::OpenOptions for OpenOptions<'inj> {
    type File = File<'inj>;

    fn read(&mut self, read: bool) -> &mut Self {
        self.inner.read(read);
        self
    }
    fn write(&mut self, write: bool) -> &mut Self {
        self.inner.write(write);
        self
    }
    fn append(&mut self, append: bool) -> &mut Self {
        self.inner.append(append);
        self
    }
    fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.inner.truncate(truncate);
        self
    }
    fn create(&mut self, create: bool) -> &mut Self {
        self.inner.create(create);
        self
    }
    fn create_new(&mut self, create_new: bool) -> &mut Self {
        self.inner.create_new(create_new);
        self
    }
    fn open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) = injector
               .as_mut()
               .map(|f| {
                        f(In::OpenOptions(AtOpenOptions::Open(self, &path.as_ref().to_owned())))
                    }) {
            r?;
        }

        self.inner
            .open(path)
            .map(|f| {
                     File {
                         injector: self.injector.clone(),
                         file_injector: self.file_injector.clone(),
                         inner: f,
                     }
                 })
    }
}

impl<'inj> unix_ext::OpenOptionsExt for OpenOptions<'inj> {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.inner.mode(mode);
        self
    }
}

/// Iterator over entries in a directory.
///
/// This struct wraps [`mem::ReadDir`] with the addition that `.next()` can potentially consume
/// [`testfs`] injected errors. See the module [documentation] for an example.
///
/// [`mem::ReadDir`]: ../mem/struct.ReadDir.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct ReadDir<'inj> {
    injector: InjectFn<'inj>,
    inner: mem::ReadDir,
}

impl<'inj> Iterator for ReadDir<'inj> {
    type Item = Result<DirEntry<'inj>>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(In::ReadDir(AtReadDir::Next(self)))) {
            if r.is_err() {
                return Some(Err(r.unwrap_err()));
            }
        }

        self.inner
            .next()
            .map(|res| {
                     res.map(|dirent| {
                                 DirEntry {
                                     injector: self.injector.clone(),
                                     inner: dirent,
                                 }
                             })
                 })
    }
}

type InjectFn<'inj> = Arc<Mutex<MaybeInjectFn<'inj>>>;
type InjectFilePartialFn<'inj> = Arc<Mutex<MaybeInjectFilePartialFn<'inj>>>;

pub type MaybeInjectFn<'inj> = Option<Box<&'inj mut FnMut(In) -> Result<()>>>;
pub type MaybeInjectFilePartialFn<'inj> = Option<Box<&'inj mut FnMut(AtFilePartial)
                                                                     -> Result<usize>>>;

/// An in memory struct that satisfies [`rsfs::FS`] and allows for injectable errors.
///
/// `FS` is thread safe and copyable. It wraps [`mem::FS`] with an ability to inject errors. This
/// should be generally useful for triggering error conditions in your code that generally are
/// untestable otherwise.
///
/// See the module [documentation] for an example.
///
/// [`rsfs::FS`]: ../trait.FS.html
/// [`mem::FS`]: ../mem/struct.FS.html
/// [documentation]: index.html
#[derive(Clone)]
pub struct FS<'inj> {
    injector: InjectFn<'inj>,
    file_injector: InjectFilePartialFn<'inj>,
    inner: mem::FS,
}

impl<'inj> FS<'inj> {
    /// Creates an empty `FS` with mode `0o777`.
    pub fn new() -> FS<'inj> {
        Self::with_mode(0o777)
    }

    /// Creates an empty `FS` with the given mode.
    pub fn with_mode(mode: u32) -> FS<'inj> {
        FS {
            injector: Arc::new(Mutex::new(None)),
            file_injector: Arc::new(Mutex::new(None)),
            inner: mem::FS::with_mode(mode),
        }
    }

    /// Changes the current working directory of the filesytsem.
    ///
    /// This call simply calls [`cd`] on the wrapped [`mem::FS`]. Because this is a function whose
    /// intent is only to setup a test filesystem, it is not possible to inject errors into this
    /// call.
    ///
    /// [`cd`]: ../mem/struct.FS.html#method.cd
    /// [`mem::FS`]: ../mem/struct.FS.html
    pub fn cd<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        self.inner.cd(path)
    }

    pub fn set_inject_fn(&mut self, f: MaybeInjectFn<'inj>) {
        *self.injector.lock() = f
    }

    pub fn set_inject_file_partial_fn(&mut self, f: MaybeInjectFilePartialFn<'inj>) {
        *self.file_injector.lock() = f
    }
}

impl<'inj> fs::GenFS for FS<'inj> {
    type DirBuilder = DirBuilder<'inj>;
    type DirEntry = DirEntry<'inj>;
    type Metadata = mem::Metadata;
    type OpenOptions = OpenOptions<'inj>;
    type Permissions = mem::Permissions;
    type ReadDir = ReadDir<'inj>;

    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<mem::Metadata> {
        let mut injector = self.injector.lock();
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(In::FS(AtFS::Metadata(&path.as_ref().to_owned())))) {
            r?
        }
        self.inner.metadata(path)
    }

    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<ReadDir<'inj>> {
        let mut injector = self.injector.lock();
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(In::FS(AtFS::ReadDir(&path.as_ref().to_owned())))) {
            r?
        }
        Ok(ReadDir {
               injector: self.injector.clone(),
               inner: self.inner.read_dir(path)?,
           })
    }

    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(In::FS(AtFS::RemoveDir(&path.as_ref().to_owned())))) {
            r?
        }
        self.inner.remove_dir(path)
    }

    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) = injector
                         .as_mut()
                         .map(|f| {
                             f(In::FS(AtFS::RemoveDirAll(
                                         &path.as_ref().to_owned())))
                         }) {
            r?
        }
        self.inner.remove_dir_all(path)
    }
    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) = injector
               .as_mut()
               .map(|f| f(In::FS(AtFS::RemoveFile(&path.as_ref().to_owned())))) {
            r?
        }
        self.inner.remove_file(path)
    }
    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) = injector
               .as_mut()
               .map(|f| {
                        f(In::FS(AtFS::Rename(&from.as_ref().to_owned(),
                                                  &to.as_ref().to_owned())))
                    }) {
            r?
        }
        self.inner.rename(from, to)
    }
    fn set_permissions<P: AsRef<Path>>(&self, path: P, perm: Self::Permissions) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FS(AtFS::SetPermissions(&path.as_ref().to_owned(), &perm)))) {
            r?
        }
        self.inner.set_permissions(path, perm)
    }
    fn new_openopts(&self) -> OpenOptions<'inj> {
        OpenOptions {
            injector: self.injector.clone(),
            file_injector: self.file_injector.clone(),
            inner: self.inner.new_openopts(),
        }
    }
    fn new_dirbuilder(&self) -> DirBuilder<'inj> {
        DirBuilder {
            injector: self.injector.clone(),
            inner: self.inner.new_dirbuilder(),
        }
    }
}

// #[cfg(test)]
// mod test {
// use super::*;
// use errors::*;
// use fs::{DirBuilder, GenFS, OpenOptions};
// use std::io::{Error, Read, Seek, SeekFrom, Write};
// use unix_ext::*;
//
// fn errs_eq(l: Error, r: Error) -> bool {
// l.raw_os_error() == r.raw_os_error()
// }
//
// #[test]
// fn basic() {
// let fs = FS::with_mode(0o300);
// assert!(fs.new_dirbuilder().mode(0o700).recursive(true).create("a/b/c").is_ok());
//
// Push a few errors (rustfmt makes this hideous)...
// fs.push_sequence(vec![// Fail creating a directory...
// Box::new(|k: In| -> Option<Result<()>> {
// match k {
// In::DirBuilder(AtDirBuilder::Create) => {
// Some(Err(ENOENT()))
// }
// _ => None,
// }
// }),
// After which, one read must succeed.
// Box::new(|k: In| -> Option<Result<()>> {
// match k {
// In::File(AtFile::Read) => Some(Ok(())),
// _ => None,
// }
// }),
// Then fail the next read.
// Box::new(|k: In| -> Option<Result<()>> {
// match k {
// In::File(AtFile::Read) => Some(Err(EACCES())),
// _ => None,
// }
// })]);
//
// open a file, write some content...
// let mut wf =
// fs.new_openopts().mode(0o600).write(true).create_new(true).open("a/f").unwrap();
// assert_eq!(wf.write(vec![0, 1, 2, 3, 4, 5].as_slice()).unwrap(), 6);
//
// open the file for reading, read some content...
// let mut rf = fs.new_openopts().read(true).open("a/f").unwrap();
// assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);
//
// let mut output = [0u8; 4];
// assert_eq!(rf.read(&mut output).unwrap(), 4);
// assert_eq!(&output, &[1, 2, 3, 4]);
//
// intermix consuming the errors with non-failures.
// assert!(errs_eq(fs.new_dirbuilder().create("a/d").unwrap_err(), ENOENT())); // error 1
// assert!(fs.new_dirbuilder().create("a/d").is_ok());
// assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);
// assert_eq!(rf.read(&mut output).unwrap(), 4); // ok 2
// assert_eq!(&output, &[1, 2, 3, 4]);
// assert_eq!(rf.seek(SeekFrom::Start(2)).unwrap(), 2);
// assert!(errs_eq(rf.read(&mut output).unwrap_err(), EACCES())); // error 3
// and now we are back to normal
// assert_eq!(rf.read(&mut output).unwrap(), 4);
// assert_eq!(&output, &[2, 3, 4, 5]);
// }
// }
//
