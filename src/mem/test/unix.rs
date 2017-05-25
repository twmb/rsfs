//! This module provides an in-memory filesystem, error injectable filesystem. It is `pub use`d in
//! `rsfs::mem::test`.

// TODO redo this entire API.

extern crate parking_lot;

use std::cmp;
use std::ffi::OsString;
use std::fmt;
use std::io::{Read, Result, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::SystemTime;

use self::parking_lot::Mutex;

use fs;
use unix_ext;
use mem::unix as mem;

/// The `testfs` is about to call a method on a file that can error.
pub enum InFile<'p> {
    Read(&'p File, &'p [u8]),
    Write(&'p File, &'p [u8]),
    ReadAt(&'p File, &'p [u8], u64),
    WriteAt(&'p File, &'p [u8], u64),
}

impl<'a> InFile<'a> {
    pub fn buf_len(&'a self) -> usize {
        match *self {
            InFile::Read(_, b) => b.len(),
            InFile::Write(_, b) => b.len(),
            InFile::ReadAt(_, b, _) => b.len(),
            InFile::WriteAt(_, b, _) => b.len(),
        }
    }
}

/// The `testfs` is about to call a method that can error.
pub enum In<'p> {
    DirBuilderCreate(&'p DirBuilder, &'p PathBuf),
    DirEntryMetadata(&'p DirEntry),
    DirEntryFileType(&'p DirEntry),
    FileSyncAll(&'p File),
    FileSyncData(&'p File),
    FileSetLen(&'p File, u64),
    FileMetadata(&'p File),
    FileTryClone(&'p File),
    FileSetPermissions(&'p File, mem::Permissions),
    FileFlush(&'p File),
    FileSeek(&'p File, &'p SeekFrom),
    MetadataModified(&'p Metadata),
    MetadataAccessed(&'p Metadata),
    MetadataCreated(&'p Metadata),
    OpenOptionsOpen(&'p OpenOptions, &'p PathBuf),
    ReadDirNext(&'p ReadDir),
    FSCanonicalize(&'p PathBuf),
    FSCopy(&'p PathBuf, &'p PathBuf),
    FSCreateDir(&'p PathBuf),
    FSCreateDirAll(&'p PathBuf),
    FSHardLink(&'p PathBuf, &'p PathBuf),
    FSMetadata(&'p PathBuf),
    FSReadDir(&'p PathBuf),
    FSReadLink(&'p PathBuf),
    FSRemoveDir(&'p PathBuf),
    FSRemoveDirAll(&'p PathBuf),
    FSRemoveFile(&'p PathBuf),
    FSRename(&'p PathBuf, &'p PathBuf),
    FSSetPermissions(&'p PathBuf, &'p mem::Permissions),
    FSSymlinkMetadata(&'p PathBuf),
    FSOpenFile(&'p PathBuf),
    FSCreateFile(&'p PathBuf),
    FSSymlink(&'p PathBuf, &'p PathBuf)
}

/// A builder used to create directories in various manners.
///
/// This struct wraps [`mem::DirBuilder`] with the addition that `.create()` can potentially
/// consume a [`testfs`] injected error. See the module [documentation] for an example.
///
/// [`mem::DirBuilder`]: ../mem/struct.DirBuilder.html
/// [`testfs`]: index.html
/// [documentation]: index.html
pub struct DirBuilder {
    injector: InjectFn,
    pub inner: mem::DirBuilder,
}

impl fmt::Debug for DirBuilder {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DirBuilder {{ inner: {:?} }}", &self.inner)
    }
}

impl fs::DirBuilder for DirBuilder {
    fn recursive(&mut self, recursive: bool) -> &mut Self {
        self.inner.recursive(recursive); self
    }
    fn create<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::DirBuilderCreate(self, &path.as_ref().to_owned()))) {
            r?;
        }
        self.inner.create(path)
    }
}

impl unix_ext::DirBuilderExt for DirBuilder {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.inner.mode(mode); self
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
pub struct DirEntry {
    injector: InjectFn,
    pub inner: mem::DirEntry,
}

impl fmt::Debug for DirEntry {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "DirEntry {{ inner: {:?} }}", &self.inner)
    }
}

impl fs::DirEntry for DirEntry {
    type Metadata = Metadata;
    type FileType = mem::FileType;

    fn path(&self) -> PathBuf {
        self.inner.path()
    }
    fn metadata(&self) -> Result<Self::Metadata> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::DirEntryMetadata(self))) {
            r?;
        }
        Ok(Metadata {
            injector: self.injector.clone(),
            inner: self.inner.metadata()?,
        })
    }
    fn file_type(&self) -> Result<Self::FileType> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::DirEntryFileType(self))) {
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
pub struct File {
    injector: InjectFn,
    file_injector: InjectFilePartialFn,
    inner: mem::File,
}

impl fmt::Debug for File {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "File {{ inner: {:?} }}", &self.inner)
    }
}

impl fs::File for File {
    type Metadata = Metadata;
    type Permissions = mem::Permissions;

    fn sync_all(&self) -> Result<()> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FileSyncAll(self))) {
            r?;
        }
        self.inner.sync_all()
    }
    fn sync_data(&self) -> Result<()> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FileSyncData(self))) {
            r?;
        }
        self.inner.sync_data()
    }
    fn set_len(&self, size: u64) -> Result<()> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FileSetLen(self, size))) {
            r?;
        }
        self.inner.set_len(size)
    }
    fn metadata(&self) -> Result<Self::Metadata> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FileMetadata(self))) {
            r?;
        }
        Ok(Metadata {
            injector: self.injector.clone(),
            inner: self.inner.metadata()?,
        })
    }
    fn try_clone(&self) -> Result<Self> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FileTryClone(self))) {
            r?;
        }
        let inner = self.inner.try_clone()?;
        Ok(File {
            injector: self.injector.clone(),
            file_injector: self.file_injector.clone(),
            inner: inner,
        })
    }
    fn set_permissions(&self, perm: Self::Permissions) -> Result<()> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FileSetPermissions(self, perm))) {
            r?;
        }
        self.inner.set_permissions(perm)
    }
}

impl unix_ext::FileExt for File {
    fn read_at(&self, buf: &mut [u8], offset: u64) -> Result<usize> {
        let mut injector = self.file_injector.lock(); // always hold for the entire fn
        let mut sz = buf.len();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(InFile::ReadAt(self, buf, offset))) {
            sz = cmp::min(r?, buf.len());
        }
        (&self.inner).read_at(&mut buf[..sz], offset)
    }
    fn write_at(&self, buf: &[u8], offset: u64) -> Result<usize> {
        let mut injector = self.file_injector.lock(); // always hold for the entire fn
        let mut sz = buf.len();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(InFile::WriteAt(self, buf, offset))) {
            sz = cmp::min(r?, buf.len());
        }
        (&self.inner).write_at(&buf[..sz], offset)
    }
}

impl Read for File {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        (&mut &*self).read(buf)
    }
}
impl Write for File {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        (&mut &*self).write(buf)
    }
    fn flush(&mut self) -> Result<()> {
        (&mut &*self).flush()
    }
}
impl Seek for File {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        (&mut &*self).seek(pos)
    }
}

impl<'a> Read for &'a File {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let mut injector = self.file_injector.lock(); // always hold for the entire fn
        // The injector may return Ok, but that we should read a small number of bytes.
        let mut sz = buf.len();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(InFile::Read(self, buf))) {
            sz = cmp::min(r?, buf.len());
        }
        (&self.inner).read(&mut buf[..sz])
    }
}

impl<'a> Write for &'a File {
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        let mut injector = self.file_injector.lock(); // always hold for the entire fn
        // The injector may return Ok, but that we should write a small number of bytes.
        let mut sz = buf.len();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(InFile::Write(self, buf))) {
            sz = cmp::min(r?, buf.len());
        }
        (&self.inner).write(&buf[..sz])
    }
    fn flush(&mut self) -> Result<()> {
        (&self.inner).flush()
    }
}

impl<'a> Seek for &'a File {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FileSeek(self, &pos))) {
            r?;
        }
        (&self.inner).seek(pos)
    }
}

#[derive(Clone)]
pub struct Metadata {
    injector: InjectFn,
    inner: mem::Metadata,
}

impl fs::Metadata for Metadata {
    type Permissions = mem::Permissions;
    type FileType    = mem::FileType;

    fn file_type(&self) -> Self::FileType {
        self.inner.file_type()
    }
    fn is_dir(&self) -> bool {
        self.inner.is_dir()
    }
    fn is_file(&self) -> bool {
        self.inner.is_file()
    }
    fn len(&self) -> u64 {
        self.inner.len()
    }
    fn permissions(&self) -> Self::Permissions {
        self.inner.permissions()
    }
    fn modified(&self) -> Result<SystemTime> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::MetadataModified(self))) {
            r?;
        }
        Ok(self.inner.modified()?)
    }
    fn accessed(&self) -> Result<SystemTime> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::MetadataAccessed(self))) {
            r?;
        }
        Ok(self.inner.accessed()?)
    }
    fn created(&self) -> Result<SystemTime> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::MetadataCreated(self))) {
            r?;
        }
        Ok(self.inner.created()?)
    }
}

impl fmt::Debug for Metadata {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Metadata {{ inner: {:?} }}", &self.inner)
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
#[derive(Clone)]
pub struct OpenOptions {
    injector: InjectFn,
    file_injector: InjectFilePartialFn,
    inner: mem::OpenOptions,
}

impl fmt::Debug for OpenOptions {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "OpenOptions {{ inner: {:?} }}", &self.inner)
    }
}

impl fs::OpenOptions for OpenOptions {
    type File = File;

    fn read(&mut self, read: bool) -> &mut Self {
        self.inner.read(read); self
    }
    fn write(&mut self, write: bool) -> &mut Self {
        self.inner.write(write); self
    }
    fn append(&mut self, append: bool) -> &mut Self {
        self.inner.append(append); self
    }
    fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.inner.truncate(truncate); self
    }
    fn create(&mut self, create: bool) -> &mut Self {
        self.inner.create(create); self
    }
    fn create_new(&mut self, create_new: bool) -> &mut Self {
        self.inner.create_new(create_new); self
    }
    fn open<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::OpenOptionsOpen(self, &path.as_ref().to_owned()))) {
            r?;
        }

        Ok(File {
            injector: self.injector.clone(),
            file_injector: self.file_injector.clone(),
            inner: self.inner.open(path)?,
        })
    }
}

impl unix_ext::OpenOptionsExt for OpenOptions {
    fn mode(&mut self, mode: u32) -> &mut Self {
        self.inner.mode(mode); self
    }
    fn custom_flags(&mut self, flags: i32) -> &mut Self {
        self.inner.custom_flags(flags); self
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
pub struct ReadDir {
    injector: InjectFn,
    inner: mem::ReadDir,
}

impl fmt::Debug for ReadDir {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ReadDir {{ inner: {:?} }}", &self.inner)
    }
}

impl Iterator for ReadDir {
    type Item = Result<DirEntry>;

    fn next(&mut self) -> Option<Self::Item> {
        let mut injector = self.injector.lock(); // always hold for the entire fn
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::ReadDirNext(self))) {
            if r.is_err() {
                return Some(Err(r.expect_err("is_err failed!")));
            }
        }
        self.inner
            .next()
            .map(|res| Ok(DirEntry {
                injector: self.injector.clone(),
                inner: res?,
            }))
    }
}

type InjectFn = Arc<Mutex<MaybeInjectFn>>;
type InjectFilePartialFn = Arc<Mutex<MaybeInjectFilePartialFn>>;

pub type MaybeInjectFn = Option<Box<FnMut(In) -> Result<()> + Send>>;
pub type MaybeInjectFilePartialFn = Option<Box<FnMut(InFile) -> Result<usize> + Send>>;

/// An in-memory struct that satisfies [`rsfs::FS`] and allows for injectable errors.
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
pub struct FS {
    injector: InjectFn,
    file_injector: InjectFilePartialFn,
    inner: mem::FS,
}

impl fmt::Debug for FS {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "FS {{ inner: {:?} }}", &self.inner)
    }
}

impl FS {
    /// Creates an empty `FS` with mode `0o777`.
    pub fn new() -> FS {
        Self::with_mode(0o777)
    }

    /// Creates an empty `FS` with the given mode.
    pub fn with_mode(mode: u32) -> FS {
        FS {
            injector: Arc::new(Mutex::new(None)),
            file_injector: Arc::new(Mutex::new(None)),
            inner: mem::FS::with_mode(mode),
        }
    }

    pub fn set_inject_fn(&mut self, f: MaybeInjectFn) {
        *self.injector.lock() = f
    }

    pub fn set_inject_file_partial_fn(&mut self, f: MaybeInjectFilePartialFn) {
        *self.file_injector.lock() = f
    }
}

impl fs::GenFS for FS {
    type DirBuilder = DirBuilder;
    type DirEntry = DirEntry;
    type Metadata = Metadata;
    type OpenOptions = OpenOptions;
    type Permissions = mem::Permissions;
    type ReadDir = ReadDir;
    type File = File;

    fn canonicalize<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSCanonicalize(&path.as_ref().to_owned()))) {
            r?
        }
        self.inner.canonicalize(path)
    }

    fn copy<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<u64> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSCopy(&from.as_ref().to_owned(), &to.as_ref().to_owned()))) {
            r?
        }
        self.inner.copy(from, to)
    }

    fn create_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSCreateDir(&path.as_ref().to_owned()))) {
            r?
        }
        self.inner.create_dir(path)
    }

    fn create_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSCreateDirAll(&path.as_ref().to_owned()))) {
            r?
        }
        self.inner.create_dir_all(path)
    }

    fn hard_link<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSHardLink(&src.as_ref().to_owned(), &dst.as_ref().to_owned()))) {
            r?
        }
        self.inner.hard_link(src, dst)
    }

    fn metadata<P: AsRef<Path>>(&self, path: P) -> Result<Metadata> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSMetadata(&path.as_ref().to_owned()))) {
            r?
        }
        Ok(Metadata {
            injector: self.injector.clone(),
            inner: self.inner.metadata(path)?,
        })
    }

    fn read_dir<P: AsRef<Path>>(&self, path: P) -> Result<ReadDir> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSReadDir(&path.as_ref().to_owned()))) {
            r?
        }
        Ok(ReadDir {
            injector: self.injector.clone(),
            inner: self.inner.read_dir(path)?,
        })
    }

    fn read_link<P: AsRef<Path>>(&self, path: P) -> Result<PathBuf> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSReadLink(&path.as_ref().to_owned()))) {
            r?
        }
        self.inner.read_link(path)
    }

    fn remove_dir<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSRemoveDir(&path.as_ref().to_owned()))) {
            r?
        }
        self.inner.remove_dir(path)
    }

    fn remove_dir_all<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FSRemoveDirAll(&path.as_ref().to_owned()))) {
            r?
        }
        self.inner.remove_dir_all(path)
    }

    fn remove_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSRemoveFile(&path.as_ref().to_owned()))) {
            r?
        }
        self.inner.remove_file(path)
    }

    fn rename<P: AsRef<Path>, Q: AsRef<Path>>(&self, from: P, to: Q) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSRename(&from.as_ref().to_owned(), &to.as_ref().to_owned()))) {
            r?
        }
        self.inner.rename(from, to)
    }

    fn set_permissions<P: AsRef<Path>>(&self, path: P, perm: Self::Permissions) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FSSetPermissions(&path.as_ref().to_owned(), &perm))) {
            r?
        }
        self.inner.set_permissions(path, perm)
    }

    fn symlink_metadata<P: AsRef<Path>>(&self, path: P) -> Result<Metadata> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
               .as_mut()
               .map(|f| f(In::FSSymlinkMetadata(&path.as_ref().to_owned()))) {
            r?
        }
        Ok(Metadata {
            injector: self.injector.clone(),
            inner: self.inner.symlink_metadata(path)?,
        })
    }

    fn new_openopts(&self) -> OpenOptions {
        OpenOptions {
            injector: self.injector.clone(),
            file_injector: self.file_injector.clone(),
            inner: self.inner.new_openopts(),
        }
    }

    fn new_dirbuilder(&self) -> DirBuilder {
        DirBuilder {
            injector: self.injector.clone(),
            inner: self.inner.new_dirbuilder(),
        }
    }

    fn open_file<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FSOpenFile(&path.as_ref().to_owned()))) {
            r?
        }
        Ok(File {
            injector: self.injector.clone(),
            file_injector: self.file_injector.clone(),
            inner: self.inner.open_file(path)?,
        })
    }

    fn create_file<P: AsRef<Path>>(&self, path: P) -> Result<Self::File> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FSCreateFile(&path.as_ref().to_owned()))) {
            r?
        }
        Ok(File {
            injector: self.injector.clone(),
            file_injector: self.file_injector.clone(),
            inner: self.inner.create_file(path)?,
        })
    }
}

impl unix_ext::GenFSExt for FS {
    fn symlink<P: AsRef<Path>, Q: AsRef<Path>>(&self, src: P, dst: Q) -> Result<()> {
        let mut injector = self.injector.lock();
        if let Some(r) =
            injector
                .as_mut()
                .map(|f| f(In::FSSymlink(&src.as_ref().to_owned(), &dst.as_ref().to_owned()))) {
            r?
        }
        Ok(self.inner.symlink(src, dst)?)
    }
}

#[cfg(test)]
mod test {
    use fs::{DirBuilder, GenFS, OpenOptions};
    use std::io::{Error, Read, Result, Seek, SeekFrom, Write};
    use std::collections::VecDeque;
    use super::*;
    use errors::*;
    use unix_ext::*;

    fn errs_eq(l: Error, r: Error) -> bool {
        l.raw_os_error() == r.raw_os_error()
    }

    #[test]
    fn basic() {
        let mut fs = FS::with_mode(0o300);
        assert!(fs.create_dir_all("a/b/c").is_ok());
        let mut wf =
        fs.new_openopts().mode(0o600).write(true).create_new(true).open("a/f").unwrap();
        assert_eq!(wf.write(b"hello").unwrap(), 5);

        let mut rf = fs.open_file("a/f").unwrap();
        assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);

        let mut output = [0u8; 4];
        assert_eq!(rf.read(&mut output).unwrap(), 4);
        assert_eq!(&output, b"ello");

        let cascade_file = Arc::new(Mutex::new(vec![]));
        let cf_clone = cascade_file.clone();
        let mut cascade_fs: VecDeque<Box<FnMut(In) -> Result<()> + Send>> = VecDeque::new();
        cascade_fs.push_back(Box::new(|_in: In| -> Result<()> {
                if let In::DirBuilderCreate(_, pb) = _in {
                    if pb.to_str().unwrap() == "a/d" {
                        return Err(ENOENT())
                    }
                }
                Ok(())
            }));
        cascade_fs.push_back(Box::new(move |_in: In| -> Result<()> {
                cf_clone.lock().push(Box::new(|_in: InFile| -> Result<usize> {
                    if let InFile::Write(_, buf) = _in {
                        return Ok((buf.len() / 2))
                    }
                    Ok(_in.buf_len())
                }));
                Ok(())
            }));

        fs.set_inject_fn(Some(Box::new(move |_in: In| -> Result<()> {
            match cascade_fs.pop_front() {
                Some(mut f) => f(_in),
                None => Ok(()),
            }
        })));
        fs.set_inject_file_partial_fn(Some(Box::new(move |_in: InFile| -> Result<usize> {
            match cascade_file.lock().pop() {
                Some(f) => f(_in),
                None => Ok(_in.buf_len()),
            }
        })));

        assert!(errs_eq(fs.new_dirbuilder().create("a/d").unwrap_err(), ENOENT())); // error 1
        assert!(fs.new_dirbuilder().create("a/d").is_ok());
        // When redoing this entire API, it'll actually be worth it to have more tests.
        //assert_eq!(rf.seek(SeekFrom::Start(1)).unwrap(), 1);
        //assert_eq!(rf.read(&mut output).unwrap(), 4); // ok 2
        //assert_eq!(&output, &[1, 2, 3, 4]);
        //assert_eq!(rf.seek(SeekFrom::Start(2)).unwrap(), 2);
        //assert!(errs_eq(rf.read(&mut output).unwrap_err(), EACCES())); // error 3
        //assert_eq!(rf.read(&mut output).unwrap(), 4);
        //assert_eq!(&output, &[2, 3, 4, 5]);
    }
}

