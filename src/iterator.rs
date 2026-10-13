use super::{Among, Left, Middle, Right};
use core::iter;

macro_rules! wrap_among {
    ($value:expr => $( $tail:tt )*) => {
        match $value {
            Left(inner) => inner.map(Left) $($tail)*,
            Middle(inner) => inner.map(Middle) $($tail)*,
            Right(inner) => inner.map(Right) $($tail)*,
        }
    };
}

/// Iterator that maps `Among` variant iterators to corresponding `Among`-wrapped items.
///
/// This struct is created by the [`Among::factor_into_iter`],
/// [`factor_iter`][Among::factor_iter],
/// and [`factor_iter_mut`][Among::factor_iter_mut] methods.
#[derive(Clone, Debug)]
pub struct IterAmong<L, M, R> {
  inner: Among<L, M, R>,
}

impl<L, M, R> IterAmong<L, M, R> {
  pub(crate) fn new(inner: Among<L, M, R>) -> Self {
    IterAmong { inner }
  }
}

impl<L, M, R, A> Extend<A> for Among<L, M, R>
where
  L: Extend<A>,
  M: Extend<A>,
  R: Extend<A>,
{
  fn extend<T>(&mut self, iter: T)
  where
    T: IntoIterator<Item = A>,
  {
    for_all!(*self, ref mut inner => inner.extend(iter))
  }
}

/// Extends three collections with values from the matching `Among` variant.
impl<A, B, C, L, M, R> Extend<Among<L, M, R>> for (A, B, C)
where
  A: Extend<L>,
  B: Extend<M>,
  C: Extend<R>,
{
  fn extend<T>(&mut self, iter: T)
  where
    T: IntoIterator<Item = Among<L, M, R>>,
  {
    iter.into_iter().for_each(move |item| match item {
      // TODO: use `Extend::extend_one` <https://github.com/rust-lang/rust/issues/72631>
      Left(item) => self.0.extend(iter::once(item)),
      Middle(item) => self.1.extend(iter::once(item)),
      Right(item) => self.2.extend(iter::once(item)),
    });
  }
}

/// Collects `Left`, `Middle`, and `Right` items into separate collections.
impl<A, B, C, L, M, R> iter::FromIterator<Among<L, M, R>> for (A, B, C)
where
  A: Default + Extend<L>,
  B: Default + Extend<M>,
  C: Default + Extend<R>,
{
  fn from_iter<T>(iter: T) -> Self
  where
    T: IntoIterator<Item = Among<L, M, R>>,
  {
    let mut collections = (A::default(), B::default(), C::default());
    collections.extend(iter);
    collections
  }
}

/// `Among<L, M, R>` is an iterator if `L`, `M`, and `R` are iterators.
impl<L, M, R> Iterator for Among<L, M, R>
where
  L: Iterator,
  M: Iterator<Item = L::Item>,
  R: Iterator<Item = L::Item>,
{
  type Item = L::Item;

  fn next(&mut self) -> Option<Self::Item> {
    for_all!(*self, ref mut inner => inner.next())
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    for_all!(*self, ref inner => inner.size_hint())
  }

  fn fold<Acc, G>(self, init: Acc, f: G) -> Acc
  where
    G: FnMut(Acc, Self::Item) -> Acc,
  {
    for_all!(self, inner => inner.fold(init, f))
  }

  fn for_each<F>(self, f: F)
  where
    F: FnMut(Self::Item),
  {
    for_all!(self, inner => inner.for_each(f))
  }

  fn count(self) -> usize {
    for_all!(self, inner => inner.count())
  }

  fn last(self) -> Option<Self::Item> {
    for_all!(self, inner => inner.last())
  }

  fn nth(&mut self, n: usize) -> Option<Self::Item> {
    for_all!(*self, ref mut inner => inner.nth(n))
  }

  fn collect<B>(self) -> B
  where
    B: iter::FromIterator<Self::Item>,
  {
    for_all!(self, inner => inner.collect())
  }

  fn partition<B, F>(self, f: F) -> (B, B)
  where
    B: Default + Extend<Self::Item>,
    F: FnMut(&Self::Item) -> bool,
  {
    for_all!(self, inner => inner.partition(f))
  }

  fn all<F>(&mut self, f: F) -> bool
  where
    F: FnMut(Self::Item) -> bool,
  {
    for_all!(*self, ref mut inner => inner.all(f))
  }

  fn any<F>(&mut self, f: F) -> bool
  where
    F: FnMut(Self::Item) -> bool,
  {
    for_all!(*self, ref mut inner => inner.any(f))
  }

  fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
  where
    P: FnMut(&Self::Item) -> bool,
  {
    for_all!(*self, ref mut inner => inner.find(predicate))
  }

  fn find_map<B, F>(&mut self, f: F) -> Option<B>
  where
    F: FnMut(Self::Item) -> Option<B>,
  {
    for_all!(*self, ref mut inner => inner.find_map(f))
  }

  fn position<P>(&mut self, predicate: P) -> Option<usize>
  where
    P: FnMut(Self::Item) -> bool,
  {
    for_all!(*self, ref mut inner => inner.position(predicate))
  }
}

impl<L, M, R> DoubleEndedIterator for Among<L, M, R>
where
  L: DoubleEndedIterator,
  M: DoubleEndedIterator<Item = L::Item>,
  R: DoubleEndedIterator<Item = L::Item>,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    for_all!(*self, ref mut inner => inner.next_back())
  }

  fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
    for_all!(*self, ref mut inner => inner.nth_back(n))
  }

  fn rfold<Acc, G>(self, init: Acc, f: G) -> Acc
  where
    G: FnMut(Acc, Self::Item) -> Acc,
  {
    for_all!(self, inner => inner.rfold(init, f))
  }

  fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
  where
    P: FnMut(&Self::Item) -> bool,
  {
    for_all!(*self, ref mut inner => inner.rfind(predicate))
  }
}

impl<L, M, R> ExactSizeIterator for Among<L, M, R>
where
  L: ExactSizeIterator,
  M: ExactSizeIterator<Item = L::Item>,
  R: ExactSizeIterator<Item = L::Item>,
{
  fn len(&self) -> usize {
    for_all!(*self, ref inner => inner.len())
  }
}

impl<L, M, R> iter::FusedIterator for Among<L, M, R>
where
  L: iter::FusedIterator,
  M: iter::FusedIterator<Item = L::Item>,
  R: iter::FusedIterator<Item = L::Item>,
{
}

impl<L, M, R> Iterator for IterAmong<L, M, R>
where
  L: Iterator,
  M: Iterator,
  R: Iterator,
{
  type Item = Among<L::Item, M::Item, R::Item>;

  fn next(&mut self) -> Option<Self::Item> {
    Some(map_among!(self.inner, ref mut inner => inner.next()?))
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    for_all!(self.inner, ref inner => inner.size_hint())
  }

  fn fold<Acc, G>(self, init: Acc, f: G) -> Acc
  where
    G: FnMut(Acc, Self::Item) -> Acc,
  {
    wrap_among!(self.inner => .fold(init, f))
  }

  fn for_each<F>(self, f: F)
  where
    F: FnMut(Self::Item),
  {
    wrap_among!(self.inner => .for_each(f))
  }

  fn count(self) -> usize {
    for_all!(self.inner, inner => inner.count())
  }

  fn last(self) -> Option<Self::Item> {
    Some(map_among!(self.inner, inner => inner.last()?))
  }

  fn nth(&mut self, n: usize) -> Option<Self::Item> {
    Some(map_among!(self.inner, ref mut inner => inner.nth(n)?))
  }

  fn collect<B>(self) -> B
  where
    B: iter::FromIterator<Self::Item>,
  {
    wrap_among!(self.inner => .collect())
  }

  fn partition<B, F>(self, f: F) -> (B, B)
  where
    B: Default + Extend<Self::Item>,
    F: FnMut(&Self::Item) -> bool,
  {
    wrap_among!(self.inner => .partition(f))
  }

  fn all<F>(&mut self, f: F) -> bool
  where
    F: FnMut(Self::Item) -> bool,
  {
    wrap_among!(&mut self.inner => .all(f))
  }

  fn any<F>(&mut self, f: F) -> bool
  where
    F: FnMut(Self::Item) -> bool,
  {
    wrap_among!(&mut self.inner => .any(f))
  }

  fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
  where
    P: FnMut(&Self::Item) -> bool,
  {
    wrap_among!(&mut self.inner => .find(predicate))
  }

  fn find_map<B, F>(&mut self, f: F) -> Option<B>
  where
    F: FnMut(Self::Item) -> Option<B>,
  {
    wrap_among!(&mut self.inner => .find_map(f))
  }

  fn position<P>(&mut self, predicate: P) -> Option<usize>
  where
    P: FnMut(Self::Item) -> bool,
  {
    wrap_among!(&mut self.inner => .position(predicate))
  }
}

impl<L, M, R> DoubleEndedIterator for IterAmong<L, M, R>
where
  L: DoubleEndedIterator,
  M: DoubleEndedIterator,
  R: DoubleEndedIterator,
{
  fn next_back(&mut self) -> Option<Self::Item> {
    Some(map_among!(self.inner, ref mut inner => inner.next_back()?))
  }

  fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
    Some(map_among!(self.inner, ref mut inner => inner.nth_back(n)?))
  }

  fn rfold<Acc, G>(self, init: Acc, f: G) -> Acc
  where
    G: FnMut(Acc, Self::Item) -> Acc,
  {
    wrap_among!(self.inner => .rfold(init, f))
  }

  fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
  where
    P: FnMut(&Self::Item) -> bool,
  {
    wrap_among!(&mut self.inner => .rfind(predicate))
  }
}

impl<L, M, R> ExactSizeIterator for IterAmong<L, M, R>
where
  L: ExactSizeIterator,
  M: ExactSizeIterator,
  R: ExactSizeIterator,
{
  fn len(&self) -> usize {
    for_all!(self.inner, ref inner => inner.len())
  }
}

impl<L, M, R> iter::FusedIterator for IterAmong<L, M, R>
where
  L: iter::FusedIterator,
  M: iter::FusedIterator,
  R: iter::FusedIterator,
{
}
