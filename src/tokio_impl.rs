use core::{
  pin::Pin,
  task::{Context, Poll},
};

use tokio::io::{self, AsyncBufRead, AsyncRead, AsyncSeek, AsyncWrite, ReadBuf};

use super::Among;

impl<L, M, R> AsyncRead for Among<L, M, R>
where
  L: AsyncRead,
  M: AsyncRead,
  R: AsyncRead,
{
  fn poll_read(
    self: Pin<&mut Self>,
    cx: &mut Context,
    buf: &mut ReadBuf<'_>,
  ) -> Poll<io::Result<()>> {
    match self.as_pin_mut() {
      Among::Left(left) => left.poll_read(cx, buf),
      Among::Middle(middle) => middle.poll_read(cx, buf),
      Among::Right(right) => right.poll_read(cx, buf),
    }
  }
}

impl<L, M, R> AsyncBufRead for Among<L, M, R>
where
  L: AsyncBufRead,
  M: AsyncBufRead,
  R: AsyncBufRead,
{
  fn poll_fill_buf(self: Pin<&mut Self>, cx: &mut Context) -> Poll<io::Result<&[u8]>> {
    match self.as_pin_mut() {
      Among::Left(left) => left.poll_fill_buf(cx),
      Among::Middle(middle) => middle.poll_fill_buf(cx),
      Among::Right(right) => right.poll_fill_buf(cx),
    }
  }

  fn consume(self: Pin<&mut Self>, amt: usize) {
    match self.as_pin_mut() {
      Among::Left(left) => left.consume(amt),
      Among::Middle(middle) => middle.consume(amt),
      Among::Right(right) => right.consume(amt),
    }
  }
}

impl<L, M, R> AsyncWrite for Among<L, M, R>
where
  L: AsyncWrite,
  M: AsyncWrite,
  R: AsyncWrite,
{
  fn poll_write(self: Pin<&mut Self>, cx: &mut Context, buf: &[u8]) -> Poll<io::Result<usize>> {
    match self.as_pin_mut() {
      Among::Left(left) => left.poll_write(cx, buf),
      Among::Middle(middle) => middle.poll_write(cx, buf),
      Among::Right(right) => right.poll_write(cx, buf),
    }
  }

  fn poll_flush(self: Pin<&mut Self>, cx: &mut Context) -> Poll<io::Result<()>> {
    match self.as_pin_mut() {
      Among::Left(left) => left.poll_flush(cx),
      Among::Middle(middle) => middle.poll_flush(cx),
      Among::Right(right) => right.poll_flush(cx),
    }
  }

  fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context) -> Poll<io::Result<()>> {
    match self.as_pin_mut() {
      Among::Left(left) => left.poll_shutdown(cx),
      Among::Middle(middle) => middle.poll_shutdown(cx),
      Among::Right(right) => right.poll_shutdown(cx),
    }
  }
}

impl<L, M, R> AsyncSeek for Among<L, M, R>
where
  L: AsyncSeek,
  M: AsyncSeek,
  R: AsyncSeek,
{
  fn start_seek(self: Pin<&mut Self>, pos: io::SeekFrom) -> io::Result<()> {
    match self.as_pin_mut() {
      Among::Left(left) => left.start_seek(pos),
      Among::Middle(middle) => middle.start_seek(pos),
      Among::Right(right) => right.start_seek(pos),
    }
  }

  fn poll_complete(self: Pin<&mut Self>, cx: &mut Context) -> Poll<io::Result<u64>> {
    match self.as_pin_mut() {
      Among::Left(left) => left.poll_complete(cx),
      Among::Middle(middle) => middle.poll_complete(cx),
      Among::Right(right) => right.poll_complete(cx),
    }
  }
}
