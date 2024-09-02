// This code is inspired and modified based on [`rayon-rs/either`](https://github.com/rayon-rs/either).

#![doc = include_str!("../README.md")]
#![no_std]

#[cfg(any(test, feature = "std"))]
extern crate std;

#[cfg(feature = "serde")]
pub mod serde_untagged;

#[cfg(feature = "serde")]
pub mod serde_untagged_optional;

#[cfg(feature = "either")]
mod either_impl;

#[cfg(all(feature = "futures-io", feature = "std"))]
mod futures_impl;

#[cfg(feature = "tokio")]
mod tokio_impl;

use core::convert::{AsMut, AsRef};
use core::fmt;
use core::future::Future;
use core::ops::Deref;
use core::ops::DerefMut;
use core::pin::Pin;

#[cfg(any(test, feature = "std"))]
use std::error::Error;
#[cfg(any(test, feature = "std"))]
use std::io::{self, BufRead, Read, Seek, SeekFrom, Write};

pub use crate::Among::{Left, Middle, Right};

/// The enum `Among` with variants `Left` and `Right` is a general purpose
/// sum type with two cases.
///
/// The `Among` type is symmetric and treats its variants the same way, without
/// preference.
/// (For representing success or error, use the regular `Result` enum instead.)
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Among<L, M, R> {
  /// A value of type `L`.
  Left(L),
  /// A value of type `M`.
  Middle(M),
  /// A value of type `R`.
  Right(R),
}

/// Evaluate the provided expression for both [`Among::Left`] and [`Among::Right`].
///
/// This macro is useful in cases where both sides of [`Among`] can be interacted with
/// in the same way even though the don't share the same type.
///
/// Syntax: `among::for_all!(` *expression* `,` *pattern* `=>` *expression* `)`
///
/// # Example
///
/// ```
/// use among::Among;
/// use std::borrow::Cow;
///
/// fn length(owned_or_borrowed: Among<String, Cow<'static, str>, &'static str>) -> usize {
///     among::for_all!(owned_or_borrowed, s => s.len())
/// }
///
/// fn main() {
///     let borrowed = Among::Right("Hello world!");
///     let owned = Among::Left("Hello world!".to_owned());
///     let mixed = Among::Middle(Cow::Borrowed("Hello world!"));
///
///     assert_eq!(length(borrowed), 12);
///     assert_eq!(length(mixed), 12);
///     assert_eq!(length(owned), 12);
/// }
/// ```
#[macro_export]
macro_rules! for_all {
  ($value:expr, $pattern:pat => $result:expr) => {
    match $value {
      $crate::Among::Middle($pattern) => $result,
      $crate::Among::Left($pattern) => $result,
      $crate::Among::Right($pattern) => $result,
    }
  };
}

macro_rules! map_among {
  ($value:expr, $pattern:pat => $result:expr) => {
    match $value {
      Left($pattern) => Left($result),
      Middle($pattern) => Middle($result),
      Right($pattern) => Right($result),
    }
  };
}

mod iterator;
pub use self::iterator::IterAmong;

mod into_among;
pub use self::into_among::IntoAmong;

impl<L: Clone, M: Clone, R: Clone> Clone for Among<L, M, R> {
  fn clone(&self) -> Self {
    match self {
      Left(inner) => Left(inner.clone()),
      Middle(inner) => Middle(inner.clone()),
      Right(inner) => Right(inner.clone()),
    }
  }

  fn clone_from(&mut self, source: &Self) {
    match (self, source) {
      (Left(dest), Left(source)) => dest.clone_from(source),
      (Right(dest), Right(source)) => dest.clone_from(source),
      (dest, source) => *dest = source.clone(),
    }
  }
}

impl<L, M, R> Among<L, M, R> {
  /// Return true if the value is the `Left` variant.
  ///
  /// ```
  /// use among::*;
  ///
  /// let values = [Left(1), Middle(b"the middle value"), Right("the right value")];
  /// assert_eq!(values[0].is_left(), true);
  /// assert_eq!(values[1].is_left(), false);
  /// assert_eq!(values[2].is_left(), false);
  /// ```
  pub fn is_left(&self) -> bool {
    match *self {
      Left(_) => true,
      _ => false,
    }
  }

  /// Return true if the value is the `Right` variant.
  ///
  /// ```
  /// use among::*;
  ///
  /// let values = [Left(1), Middle(b"the middle value"), Right("the right value")];
  /// assert_eq!(values[0].is_right(), false);
  /// assert_eq!(values[1].is_right(), false);
  /// assert_eq!(values[2].is_right(), true);
  /// ```
  pub fn is_right(&self) -> bool {
    match *self {
      Right(_) => true,
      _ => false,
    }
  }

  /// Return true if the value is the `Right` variant.
  ///
  /// ```
  /// use among::*;
  ///
  /// let values = [Left(1), Middle(b"the middle value"), Right("the right value")];
  /// assert_eq!(values[0].is_middle(), false);
  /// assert_eq!(values[1].is_middle(), true);
  /// assert_eq!(values[2].is_middle(), false);
  /// ```
  pub fn is_middle(&self) -> bool {
    match *self {
      Middle(_) => true,
      _ => false,
    }
  }

  /// Convert the left side of `Among<L, M, R>` to an `Option<L>`.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, i64, ()> = Left("some value");
  /// assert_eq!(left.left(),  Some("some value"));
  ///
  /// let right: Among<(), i64, _> = Right(321);
  /// assert_eq!(right.left(), None);
  ///
  /// let middle: Among<(), i64, ()> = Middle(-321);
  /// assert_eq!(middle.left(), None);
  /// ```
  pub fn left(self) -> Option<L> {
    match self {
      Left(l) => Some(l),
      _ => None,
    }
  }

  /// Convert the middle of `Among<L, M, R>` to an `Option<M>`.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, i64, ()> = Left("some value");
  /// assert_eq!(left.middle(),  None);
  ///
  /// let right: Among<(), i64, _> = Right(321);
  /// assert_eq!(right.middle(), None);
  ///
  /// let middle: Among<(), i64, ()> = Middle(-321);
  /// assert_eq!(middle.middle(), Some(-321));
  /// ```
  pub fn middle(self) -> Option<M> {
    match self {
      Middle(m) => Some(m),
      _ => None,
    }
  }

  /// Convert the right side of `Among<L, M, R>` to an `Option<R>`.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, i64, ()> = Left("some value");
  /// assert_eq!(left.right(),  None);
  ///
  /// let middle: Among<(), i64, ()> = Middle(-321);
  /// assert_eq!(middle.right(), None);
  ///
  /// let right: Among<(), i64, _> = Right(321);
  /// assert_eq!(right.right(), Some(321));
  /// ```
  pub fn right(self) -> Option<R> {
    match self {
      Right(r) => Some(r),
      _ => None,
    }
  }

  /// Convert `&Among<L, M, R>` to `Among<&L, &M, &R>`.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, i64, ()> = Left("some value");
  /// assert_eq!(left.as_ref(), Left(&"some value"));
  ///
  /// let right: Among<(), i64, _> = Right("some value");
  /// assert_eq!(right.as_ref(), Right(&"some value"));
  ///
  /// let middle: Among<(), _, ()> = Middle(-321);
  /// assert_eq!(middle.as_ref(), Middle(&-321));
  /// ```
  pub fn as_ref(&self) -> Among<&L, &M, &R> {
    match *self {
      Left(ref inner) => Left(inner),
      Middle(ref inner) => Middle(inner),
      Right(ref inner) => Right(inner),
    }
  }

  /// Convert `&mut Among<L, M, R>` to `Among<&mut L, &mut M, &mut R>`.
  ///
  /// ```
  /// use among::*;
  ///
  /// fn mutate_left(value: &mut Among<u32, u32, u32>) {
  ///     if let Some(l) = value.as_mut().left() {
  ///         *l = 999;
  ///     }
  /// }
  ///
  /// let mut left = Left(123);
  /// let mut middle = Middle(123);
  /// let mut right = Right(123);
  ///
  /// mutate_left(&mut left);
  /// mutate_left(&mut right);
  /// mutate_left(&mut middle);
  /// assert_eq!(left, Left(999));
  /// assert_eq!(right, Right(123));
  /// assert_eq!(middle, Middle(123));
  /// ```
  pub fn as_mut(&mut self) -> Among<&mut L, &mut M, &mut R> {
    match *self {
      Left(ref mut inner) => Left(inner),
      Middle(ref mut inner) => Middle(inner),
      Right(ref mut inner) => Right(inner),
    }
  }

  /// Convert `Pin<&Among<L, M, R>>` to `Among<Pin<&L>, Pin<&M>, Pin<&R>>`,
  /// pinned projections of the inner variants.
  pub fn as_pin_ref(self: Pin<&Self>) -> Among<Pin<&L>, Pin<&M>, Pin<&R>> {
    // SAFETY: We can use `new_unchecked` because the `inner` parts are
    // guaranteed to be pinned, as they come from `self` which is pinned.
    unsafe {
      match *Pin::get_ref(self) {
        Left(ref inner) => Left(Pin::new_unchecked(inner)),
        Middle(ref inner) => Middle(Pin::new_unchecked(inner)),
        Right(ref inner) => Right(Pin::new_unchecked(inner)),
      }
    }
  }

  /// Convert `Pin<&mut Among<L, M, R>>` to `Among<Pin<&mut L>, Pin<&mut M>, Pin<&mut R>>`,
  /// pinned projections of the inner variants.
  pub fn as_pin_mut(self: Pin<&mut Self>) -> Among<Pin<&mut L>, Pin<&mut M>, Pin<&mut R>> {
    // SAFETY: `get_unchecked_mut` is fine because we don't move anything.
    // We can use `new_unchecked` because the `inner` parts are guaranteed
    // to be pinned, as they come from `self` which is pinned, and we never
    // offer an unpinned `&mut L` or `&mut R` through `Pin<&mut Self>`. We
    // also don't have an implementation of `Drop`, nor manual `Unpin`.
    unsafe {
      match *Pin::get_unchecked_mut(self) {
        Left(ref mut inner) => Left(Pin::new_unchecked(inner)),
        Middle(ref mut inner) => Middle(Pin::new_unchecked(inner)),
        Right(ref mut inner) => Right(Pin::new_unchecked(inner)),
      }
    }
  }

  /// Convert `Among<L, M, R>` to `Among<R, M, L>`.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, i64, ()> = Left(123);
  /// assert_eq!(left.flip(), Right(123));
  ///
  /// let right: Among<(), i64, _> = Right("some value");
  /// assert_eq!(right.flip(), Left("some value"));
  /// ```
  pub fn flip(self) -> Among<R, M, L> {
    match self {
      Left(l) => Right(l),
      Right(r) => Left(r),
      Middle(m) => Middle(m),
    }
  }

  /// Apply the function `f` on the value in the `Left` variant if it is present rewrapping the
  /// result in `Left`.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, u32, u32> = Left(123);
  /// assert_eq!(left.map_left(|x| x * 2), Left(246));
  ///
  /// let right: Among<u32, u32,  _> = Right(123);
  /// assert_eq!(right.map_left(|x| x * 2), Right(123));
  ///
  /// let middle: Among<u32, _, u32> = Middle(123);
  /// assert_eq!(middle.map_left(|x| x * 3), Middle(123));
  /// ```
  pub fn map_left<F, N>(self, f: F) -> Among<N, M, R>
  where
    F: FnOnce(L) -> N,
  {
    match self {
      Left(l) => Left(f(l)),
      Middle(m) => Middle(m),
      Right(r) => Right(r),
    }
  }

  /// Apply the function `f` on the value in the `Middle` variant if it is present rewrapping the
  /// result in `Middle`.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, u32, u32> = Left(123);
  /// assert_eq!(left.map_middle(|x| x * 2), Left(123));
  ///
  /// let right: Among<u32, u32,  _> = Right(123);
  /// assert_eq!(right.map_middle(|x| x * 2), Right(123));
  ///
  /// let middle: Among<u32, _, u32> = Middle(123);
  /// assert_eq!(middle.map_middle(|x| x * 3), Middle(369));
  /// ```
  pub fn map_middle<F, N>(self, f: F) -> Among<L, N, R>
  where
    F: FnOnce(M) -> N,
  {
    match self {
      Left(l) => Left(l),
      Middle(m) => Middle(f(m)),
      Right(r) => Right(r),
    }
  }

  /// Apply the function `f` on the value in the `Right` variant if it is present rewrapping the
  /// result in `Right`.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, u32, u32> = Left(123);
  /// assert_eq!(left.map_right(|x| x * 2), Left(123));
  ///
  /// let right: Among<u32, u32, _> = Right(123);
  /// assert_eq!(right.map_right(|x| x * 2), Right(246));
  ///
  /// let middle: Among<u32, _, u32> = Middle(123);
  /// assert_eq!(middle.map_right(|x| x * 3), Middle(123));
  /// ```
  pub fn map_right<F, S>(self, f: F) -> Among<L, M, S>
  where
    F: FnOnce(R) -> S,
  {
    match self {
      Left(l) => Left(l),
      Middle(m) => Middle(m),
      Right(r) => Right(f(r)),
    }
  }

  /// Apply the functions `f` and `g` to the `Left` and `Right` variants
  /// respectively. This is equivalent to
  /// [bimap](https://hackage.haskell.org/package/bifunctors-5/docs/Data-Bifunctor.html)
  /// in functional programming.
  ///
  /// ```
  /// use among::*;
  ///
  /// let f = |s: String| s.len();
  /// let h = |t: u8| t.to_string();
  /// let g = |u: usize| u * 2;
  ///
  /// let left: Among<String, usize, u8> = Left("loopy".into());
  /// assert_eq!(left.map_among(f, g, h), Left(5));
  ///
  /// let right: Among<String, usize, u8> = Right(42);
  /// assert_eq!(right.map_among(f, g, h), Right("42".into()));
  /// ```
  pub fn map_among<F, G, H, S, T, U>(self, f: F, g: G, h: H) -> Among<S, T, U>
  where
    F: FnOnce(L) -> S,
    G: FnOnce(M) -> T,
    H: FnOnce(R) -> U,
  {
    match self {
      Left(l) => Left(f(l)),
      Middle(m) => Middle(g(m)),
      Right(r) => Right(h(r)),
    }
  }

  /// Similar to [`map_among`][Self::map_among], with an added context `ctx` accessible to
  /// both functions.
  ///
  /// ```
  /// use among::*;
  ///
  /// let mut sum = 0;
  ///
  /// // Both closures want to update the same value, so pass it as context.
  /// let mut f = |sum: &mut usize, s: String| { *sum += s.len(); s.to_uppercase() };
  /// let mut g = |sum: &mut usize, i: i32| { *sum += i as usize; i.to_string() };
  /// let mut h = |sum: &mut usize, u: usize| { *sum += u; u.to_string() };
  ///
  /// let left: Among<String, i32, usize> = Left("loopy".into());
  /// assert_eq!(left.map_among_with(&mut sum, &mut f, &mut g, &mut h), Left("LOOPY".into()));
  ///
  /// let right: Among<String, i32, usize> = Right(42);
  /// assert_eq!(right.map_among_with(&mut sum, &mut f, &mut g, &mut h), Right("42".into()));
  ///
  /// let middle: Among<String, i32, usize> = Middle(3);
  /// assert_eq!(middle.map_among_with(&mut sum, &mut f, &mut g, &mut h), Middle("3".into()));
  ///
  /// assert_eq!(sum, 50);
  /// ```
  pub fn map_among_with<Ctx, F, G, H, S, T, U>(self, ctx: Ctx, f: F, g: G, h: H) -> Among<S, T, U>
  where
    F: FnOnce(Ctx, L) -> S,
    G: FnOnce(Ctx, M) -> T,
    H: FnOnce(Ctx, R) -> U,
  {
    match self {
      Left(l) => Left(f(ctx, l)),
      Middle(m) => Middle(g(ctx, m)),
      Right(r) => Right(h(ctx, r)),
    }
  }

  /// Apply one of three functions depending on contents, unifying their result. If the value is
  /// `Left(L)` then the first function `f` is applied; if it is `Middle(M)` then the second function `g` is applied;
  /// if it is `Right(R)` then the third function `h` is applied.
  ///
  /// ```
  /// use among::*;
  ///
  /// fn square(n: u32) -> i32 { (n * n) as i32 }
  /// fn negate(n: i32) -> i32 { -n }
  /// fn cube(n: u64) -> i32 { (n * n * n) as i32 }
  ///
  /// let left: Among<u32, u64, i32> = Left(4);
  /// assert_eq!(left.among(square, cube, negate), 16);
  ///
  /// let right: Among<u32, u64, i32> = Right(-4);
  /// assert_eq!(right.among(square, cube, negate), 4);
  ///
  /// let middle: Among<u32, u64, i32> = Middle(3);
  /// assert_eq!(middle.among(square, cube, negate), 27);
  /// ```
  pub fn among<F, G, H, T>(self, f: F, g: G, h: H) -> T
  where
    F: FnOnce(L) -> T,
    G: FnOnce(M) -> T,
    H: FnOnce(R) -> T,
  {
    match self {
      Left(l) => f(l),
      Middle(m) => g(m),
      Right(r) => h(r),
    }
  }

  /// Like [`among`][Self::among], but provide some context to whichever of the
  /// functions ends up being called.
  ///
  /// ```
  /// // In this example, the context is a mutable reference
  /// use among::*;
  ///
  /// let mut result = Vec::new();
  ///
  /// let values = vec![Left(2), Middle(-3), Right(2.7)];
  ///
  /// for value in values {
  ///     value.among_with(&mut result,
  ///                       |ctx, integer| ctx.push(integer),
  ///                       |ctx, neg| ctx.push(neg),
  ///                       |ctx, real| ctx.push(f64::round(real) as i32));
  /// }
  ///
  /// assert_eq!(result, vec![2, -3, 3]);
  /// ```
  pub fn among_with<Ctx, F, G, H, T>(self, ctx: Ctx, f: F, g: G, h: H) -> T
  where
    F: FnOnce(Ctx, L) -> T,
    G: FnOnce(Ctx, M) -> T,
    H: FnOnce(Ctx, R) -> T,
  {
    match self {
      Left(l) => f(ctx, l),
      Middle(m) => g(ctx, m),
      Right(r) => h(ctx, r),
    }
  }

  /// Apply the function `f` on the value in the `Left` variant if it is present.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, u32, u32> = Left(123);
  /// assert_eq!(left.left_and_then::<_, ()>(|x| Right(x * 2)), Right(246));
  ///
  /// let right: Among<u32, u32, _> = Right(123);
  /// assert_eq!(right.left_and_then(|x| Right::<(), _, _>(x * 2)), Right(123));
  /// ```
  pub fn left_and_then<F, S>(self, f: F) -> Among<S, M, R>
  where
    F: FnOnce(L) -> Among<S, M, R>,
  {
    match self {
      Left(l) => f(l),
      Middle(m) => Middle(m),
      Right(r) => Right(r),
    }
  }

  /// Apply the function `f` on the value in the `Middle` variant if it is present.
  ///
  /// ```
  /// use among::*;
  ///
  /// let middle: Among<u32, _, u32> = Middle(123);
  /// assert_eq!(middle.middle_and_then::<_, ()>(|x| Right(x * 2)), Right(246));
  ///
  /// let right: Among<u32, u32, _> = Right(123);
  /// assert_eq!(right.middle_and_then(|x| Right::<_, (), _>(x * 2)), Right(123));
  /// ```
  pub fn middle_and_then<F, S>(self, f: F) -> Among<L, S, R>
  where
    F: FnOnce(M) -> Among<L, S, R>,
  {
    match self {
      Left(l) => Left(l),
      Middle(m) => f(m),
      Right(r) => Right(r),
    }
  }

  /// Apply the function `f` on the value in the `Right` variant if it is present.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, u32, u32> = Left(123);
  /// assert_eq!(left.right_and_then(|x| Right(x * 2)), Left(123));
  ///
  /// let right: Among<u32, u32, _> = Right(123);
  /// assert_eq!(right.right_and_then(|x| Right(x * 2)), Right(246));
  /// ```
  pub fn right_and_then<F, S>(self, f: F) -> Among<L, M, S>
  where
    F: FnOnce(R) -> Among<L, M, S>,
  {
    match self {
      Left(l) => Left(l),
      Middle(m) => Middle(m),
      Right(r) => f(r),
    }
  }

  /// Convert the inner value to an iterator.
  ///
  /// This requires the `Left`, `Middle` and `Right` iterators to have the same item type.
  /// See [`factor_into_iter`][Among::factor_into_iter] to iterate different types.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<Vec<u32>, Vec<u32>, Vec<u32>> = Left(vec![1, 2, 3, 4, 5]);
  /// let mut right: Among<Vec<u32>, Vec<u32>, Vec<u32>> = Right(vec![]);
  /// right.extend(left.into_iter());
  /// assert_eq!(right, Right(vec![1, 2, 3, 4, 5]));
  /// ```
  #[allow(clippy::should_implement_trait)]
  pub fn into_iter(self) -> Among<L::IntoIter, M::IntoIter, R::IntoIter>
  where
    L: IntoIterator,
    M: IntoIterator<Item = L::Item>,
    R: IntoIterator<Item = L::Item>,
  {
    map_among!(self, inner => inner.into_iter())
  }

  /// Borrow the inner value as an iterator.
  ///
  /// This requires the `Left`, `Middle` and `Right` iterators to have the same item type.
  /// See [`factor_iter`][Among::factor_iter] to iterate different types.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, &[u32], &[u32]> = Left(vec![2, 3]);
  /// let mut right: Among<Vec<u32>, &[u32], _> = Right(&[4, 5][..]);
  /// let mut all = vec![1];
  /// all.extend(left.iter());
  /// all.extend(right.iter());
  /// assert_eq!(all, vec![1, 2, 3, 4, 5]);
  /// ```
  pub fn iter(
    &self,
  ) -> Among<
    <&L as IntoIterator>::IntoIter,
    <&M as IntoIterator>::IntoIter,
    <&R as IntoIterator>::IntoIter,
  >
  where
    for<'a> &'a L: IntoIterator,
    for<'a> &'a M: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
    for<'a> &'a R: IntoIterator<Item = <&'a L as IntoIterator>::Item>,
  {
    map_among!(self, inner => inner.into_iter())
  }

  /// Mutably borrow the inner value as an iterator.
  ///
  /// This requires the `Left`, `Middle` and `Right` iterators to have the same item type.
  /// See [`factor_iter_mut`][Among::factor_iter_mut] to iterate different types.
  ///
  /// ```
  /// use among::*;
  ///
  /// let mut left: Among<_, Vec<u32>, &mut [u32]> = Left(vec![2, 3]);
  /// for l in left.iter_mut() {
  ///     *l *= *l
  /// }
  /// assert_eq!(left, Left(vec![4, 9]));
  ///
  /// let mut inner = [4, 5];
  /// let mut right: Among<Vec<u32>, Vec<u32>, _> = Right(&mut inner[..]);
  /// for r in right.iter_mut() {
  ///     *r *= *r
  /// }
  /// assert_eq!(inner, [16, 25]);
  ///
  /// let mut inner = [6, 7];
  /// let mut middle: Among<Vec<u32>, _, Vec<u32>> = Middle(&mut inner[..]);
  /// for r in middle.iter_mut() {
  ///     *r *= *r
  /// }
  /// assert_eq!(inner, [36, 49]);
  /// ```
  pub fn iter_mut(
    &mut self,
  ) -> Among<
    <&mut L as IntoIterator>::IntoIter,
    <&mut M as IntoIterator>::IntoIter,
    <&mut R as IntoIterator>::IntoIter,
  >
  where
    for<'a> &'a mut L: IntoIterator,
    for<'a> &'a mut M: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
    for<'a> &'a mut R: IntoIterator<Item = <&'a mut L as IntoIterator>::Item>,
  {
    map_among!(self, inner => inner.into_iter())
  }

  /// Converts an `Among` of `Iterator`s to be an `Iterator` of `Among`s
  ///
  /// Unlike [`into_iter`][Among::into_iter], this does not require the
  /// `Left` and `Right` iterators to have the same item type.
  ///
  /// ```
  /// use among::*;
  /// let left: Among<_, Box<[u8]>, Vec<u8>> = Left(&["hello"]);
  /// assert_eq!(left.factor_into_iter().next(), Some(Left(&"hello")));

  /// let right: Among<&[&str], Box<[u8]>, _> = Right(vec![0, 1]);
  /// assert_eq!(right.factor_into_iter().collect::<Vec<_>>(), vec![Right(0), Right(1)]);
  ///
  /// ```
  // TODO(MSRV): doc(alias) was stabilized in Rust 1.48
  // #[doc(alias = "transpose")]
  pub fn factor_into_iter(self) -> IterAmong<L::IntoIter, M::IntoIter, R::IntoIter>
  where
    L: IntoIterator,
    M: IntoIterator,
    R: IntoIterator,
  {
    IterAmong::new(map_among!(self, inner => inner.into_iter()))
  }

  /// Borrows an `Among` of `Iterator`s to be an `Iterator` of `Among`s
  ///
  /// Unlike [`iter`][Among::iter], this does not require the
  /// `Left`, `Middle` and `Right` iterators to have the same item type.
  ///
  /// ```
  /// use among::*;
  /// let left: Among<_, Box<[u8]>, Vec<u8>> = Left(["hello"]);
  /// assert_eq!(left.factor_iter().next(), Some(Left(&"hello")));

  /// let right: Among<[&str; 2], Box<[u8]>, _> = Right(vec![0, 1]);
  /// assert_eq!(right.factor_iter().collect::<Vec<_>>(), vec![Right(&0), Right(&1)]);
  ///
  /// ```
  pub fn factor_iter(
    &self,
  ) -> IterAmong<
    <&L as IntoIterator>::IntoIter,
    <&M as IntoIterator>::IntoIter,
    <&R as IntoIterator>::IntoIter,
  >
  where
    for<'a> &'a L: IntoIterator,
    for<'a> &'a M: IntoIterator,
    for<'a> &'a R: IntoIterator,
  {
    IterAmong::new(map_among!(self, inner => inner.into_iter()))
  }

  /// Mutably borrows an `Among` of `Iterator`s to be an `Iterator` of `Among`s
  ///
  /// Unlike [`iter_mut`][Among::iter_mut], this does not require the
  /// `Left`, `Middle` and `Right` iterators to have the same item type.
  ///
  /// ```
  /// use among::*;
  /// let mut left: Among<_, Box<[u8]>, Vec<u8>> = Left(["hello"]);
  /// left.factor_iter_mut().for_each(|x| *x.unwrap_left() = "goodbye");
  /// assert_eq!(left, Left(["goodbye"]));

  /// let mut right: Among<[&str; 2], Box<[u8]>, _> = Right(vec![0, 1, 2]);
  /// right.factor_iter_mut().for_each(|x| if let Right(r) = x { *r = -*r; });
  /// assert_eq!(right, Right(vec![0, -1, -2]));
  ///
  /// ```
  pub fn factor_iter_mut(
    &mut self,
  ) -> IterAmong<
    <&mut L as IntoIterator>::IntoIter,
    <&mut M as IntoIterator>::IntoIter,
    <&mut R as IntoIterator>::IntoIter,
  >
  where
    for<'a> &'a mut L: IntoIterator,
    for<'a> &'a mut M: IntoIterator,
    for<'a> &'a mut R: IntoIterator,
  {
    IterAmong::new(map_among!(self, inner => inner.into_iter()))
  }

  /// Return left value or given value
  ///
  /// Arguments passed to `left_or` are eagerly evaluated; if you are passing
  /// the result of a function call, it is recommended to use
  /// [`left_or_else`][Self::left_or_else], which is lazily evaluated.
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let left: Among<&str, &str, &str> = Left("left");
  /// assert_eq!(left.left_or("foo"), "left");
  ///
  /// let right: Among<&str, &str, &str> = Right("right");
  /// assert_eq!(right.left_or("left"), "left");
  ///
  /// let middle: Among<&str, &str, &str> = Middle("middle");
  /// assert_eq!(middle.left_or("left"), "left");
  /// ```
  pub fn left_or(self, other: L) -> L {
    match self {
      Among::Left(l) => l,
      Among::Right(_) => other,
      Among::Middle(_) => other,
    }
  }

  /// Return left or a default
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let left: Among<String, i32, u32> = Left("left".to_string());
  /// assert_eq!(left.left_or_default(), "left");
  ///
  /// let right: Among<String, i32, u32> = Right(42);
  /// assert_eq!(right.left_or_default(), String::default());
  ///
  /// let middle: Among<String, i32, u32> = Middle(-42);
  /// assert_eq!(middle.left_or_default(), String::default());
  /// ```
  pub fn left_or_default(self) -> L
  where
    L: Default,
  {
    match self {
      Among::Left(l) => l,
      Among::Right(_) => L::default(),
      Among::Middle(_) => L::default(),
    }
  }

  /// Returns left value or computes it from a closure
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let left: Among<String, i32, u32> = Left("3".to_string());
  /// assert_eq!(left.left_or_else(|_| unreachable!(), |_| unreachable!()), "3");
  ///
  /// let right: Among<String, i32, u32> = Right(3);
  /// assert_eq!(right.left_or_else(|x| x.to_string(), |x| x.to_string()), "3");
  ///
  /// let middle: Among<String, i32, u32> = Middle(3);
  /// assert_eq!(middle.left_or_else(|x| x.to_string(), |x| x.to_string()), "3");
  /// ```
  pub fn left_or_else<F, G>(self, f: F, g: G) -> L
  where
    F: FnOnce(R) -> L,
    G: FnOnce(M) -> L,
  {
    match self {
      Among::Left(l) => l,
      Among::Right(r) => f(r),
      Among::Middle(m) => g(m),
    }
  }

  /// Return middle value or given value
  ///
  /// Arguments passed to `middle_or` are eagerly evaluated; if you are passing
  /// the result of a function call, it is recommended to use
  /// [`middle_or_else`][Self::middle_or_else], which is lazily evaluated.
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let right: Among<&str, &str, &str> = Right("right");
  /// assert_eq!(right.middle_or("middle"), "middle");
  ///
  /// let left: Among<&str, &str, &str> = Left("left");
  /// assert_eq!(left.middle_or("middle"), "middle");
  ///
  /// let middle: Among<&str, &str, &str> = Middle("middle");
  /// assert_eq!(middle.middle_or("foo"), "middle");
  /// ```
  pub fn middle_or(self, other: M) -> M {
    match self {
      Among::Middle(m) => m,
      _ => other,
    }
  }

  /// Return middle or a default
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let left: Among<String, i32, u32> = Left("left".to_string());
  /// assert_eq!(left.middle_or_default(), i32::default());
  ///
  /// let right: Among<String, i32, u32> = Right(42);
  /// assert_eq!(right.middle_or_default(), i32::default());
  ///
  /// let middle: Among<String, i32, u32> = Middle(-42);
  /// assert_eq!(middle.middle_or_default(), -42);
  /// ```
  pub fn middle_or_default(self) -> M
  where
    M: Default,
  {
    match self {
      Among::Middle(m) => m,
      _ => M::default(),
    }
  }

  /// Returns middle value or computes it from a closure
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let left: Among<String, i32, String> = Left("3".to_string());
  /// assert_eq!(left.middle_or_else(|x| x.parse().unwrap(), |x| x.parse().unwrap()), 3);
  ///
  /// let right: Among<String, i32, String> = Right("3".to_string());
  /// assert_eq!(right.middle_or_else(|x| x.parse().unwrap(), |x| x.parse().unwrap()), 3);
  ///
  /// let middle: Among<String, i32, String> = Middle(-3);
  /// assert_eq!(middle.middle_or_else(|_| unreachable!(), |_| unreachable!()), -3);
  /// ```
  pub fn middle_or_else<F, G>(self, f: F, g: G) -> M
  where
    F: FnOnce(L) -> M,
    G: FnOnce(R) -> M,
  {
    match self {
      Among::Left(l) => f(l),
      Among::Middle(m) => m,
      Among::Right(r) => g(r),
    }
  }

  /// Return right value or given value
  ///
  /// Arguments passed to `right_or` are eagerly evaluated; if you are passing
  /// the result of a function call, it is recommended to use
  /// [`right_or_else`][Self::right_or_else], which is lazily evaluated.
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let right: Among<&str, &str, &str> = Right("right");
  /// assert_eq!(right.right_or("foo"), "right");
  ///
  /// let left: Among<&str, &str, &str> = Left("left");
  /// assert_eq!(left.right_or("right"), "right");
  ///
  /// let middle: Among<&str, &str, &str> = Middle("middle");
  /// assert_eq!(middle.right_or("right"), "right");
  /// ```
  pub fn right_or(self, other: R) -> R {
    match self {
      Among::Left(_) => other,
      Among::Middle(_) => other,
      Among::Right(r) => r,
    }
  }

  /// Return right or a default
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let left: Among<String, i32, u32> = Left("left".to_string());
  /// assert_eq!(left.right_or_default(), u32::default());
  ///
  /// let right: Among<String, i32, u32> = Right(42);
  /// assert_eq!(right.right_or_default(), 42);
  ///
  /// let middle: Among<String, i32, u32> = Middle(-42);
  /// assert_eq!(middle.right_or_default(), u32::default());
  /// ```
  pub fn right_or_default(self) -> R
  where
    R: Default,
  {
    match self {
      Among::Left(_) => R::default(),
      Among::Middle(_) => R::default(),
      Among::Right(r) => r,
    }
  }

  /// Returns right value or computes it from a closure
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let left: Among<String, &str, u32> = Left("3".to_string());
  /// assert_eq!(left.right_or_else(|x| x.parse().unwrap(), |x| x.parse().unwrap()), 3);
  ///
  /// let right: Among<String, &str, u32> = Right(3);
  /// assert_eq!(right.right_or_else(|_| unreachable!(), |_| unreachable!()), 3);
  ///
  /// let middle: Among<String, &str, u32> = Middle("3");
  /// assert_eq!(middle.right_or_else(|x| x.parse().unwrap(), |x| x.parse().unwrap()), 3);
  /// ```
  pub fn right_or_else<F, G>(self, f: F, g: G) -> R
  where
    F: FnOnce(L) -> R,
    G: FnOnce(M) -> R,
  {
    match self {
      Among::Left(l) => f(l),
      Among::Middle(m) => g(m),
      Among::Right(r) => r,
    }
  }

  /// Returns the left value
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let left: Among<_, (), ()> = Left(3);
  /// assert_eq!(left.unwrap_left(), 3);
  /// ```
  ///
  /// # Panics
  ///
  /// When `Among` is a `Right` value
  ///
  /// ```should_panic
  /// # use among::*;
  /// let right: Among<(), (), _> = Right(3);
  /// right.unwrap_left();
  /// ```
  ///
  /// ```should_panic
  /// # use among::*;
  /// let middle: Among<(), _, ()> = Middle(3);
  /// middle.unwrap_left();
  /// ```
  pub fn unwrap_left(self) -> L
  where
    M: core::fmt::Debug,
    R: core::fmt::Debug,
  {
    match self {
      Among::Left(l) => l,
      Among::Middle(m) => {
        panic!(
          "called `Among::unwrap_middle()` on a `Middle` value: {:?}",
          m
        )
      }
      Among::Right(r) => {
        panic!("called `Among::unwrap_left()` on a `Right` value: {:?}", r)
      }
    }
  }

  /// Returns the right value
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let right: Among<(), (), _> = Right(3);
  /// assert_eq!(right.unwrap_right(), 3);
  /// ```
  ///
  /// # Panics
  ///
  /// When `Among` is a `Left` value
  ///
  /// ```should_panic
  /// # use among::*;
  /// let left: Among<_, (), ()> = Left(3);
  /// left.unwrap_right();
  /// ```
  ///
  /// ```should_panic
  /// # use among::*;
  /// let middle: Among<(), _, ()> = Middle(3);
  /// middle.unwrap_right();
  /// ```
  pub fn unwrap_right(self) -> R
  where
    L: core::fmt::Debug,
    M: core::fmt::Debug,
  {
    match self {
      Among::Right(r) => r,
      Among::Middle(m) => panic!(
        "called `Among::unwrap_middle()` on a `Middle` value: {:?}",
        m
      ),
      Among::Left(l) => panic!("called `Among::unwrap_right()` on a `Left` value: {:?}", l),
    }
  }

  /// Returns the left value
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let left: Among<_, (), ()> = Left(3);
  /// assert_eq!(left.expect_left("value was not Left"), 3);
  /// ```
  ///
  /// # Panics
  ///
  /// When `Among` is a `Right` value
  ///
  /// ```should_panic
  /// # use among::*;
  /// let right: Among<(), (), _> = Right(3);
  /// right.expect_left("value was not Left");
  /// ```
  ///
  /// When `Among` is a `Middle` value
  ///
  /// ```should_panic
  /// # use among::*;
  /// let middle: Among<(), _, ()> = Middle(3);
  /// middle.expect_left("value was not Left");
  /// ```
  pub fn expect_left(self, msg: &str) -> L
  where
    M: core::fmt::Debug,
    R: core::fmt::Debug,
  {
    match self {
      Among::Left(l) => l,
      Among::Middle(m) => panic!("{}: {:?}", msg, m),
      Among::Right(r) => panic!("{}: {:?}", msg, r),
    }
  }

  /// Returns the left value
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let middle: Among<(), _, ()> = Middle(3);
  /// assert_eq!(middle.expect_middle("value was Middle"), 3);
  /// ```
  ///
  /// # Panics
  ///
  /// When `Among` is a `Right` value
  ///
  /// ```should_panic
  /// # use among::*;
  /// let right: Among<(), (), _> = Right(3);
  /// right.expect_middle("value was not Middle");
  /// ```
  ///
  /// When `Among` is a `Left` value
  ///
  /// ```should_panic
  /// # use among::*;
  /// let left: Among<_, (), ()> = Left(3);
  /// left.expect_middle("value was not Middle");
  /// ```
  pub fn expect_middle(self, msg: &str) -> M
  where
    L: core::fmt::Debug,
    R: core::fmt::Debug,
  {
    match self {
      Among::Left(l) => panic!("{}: {:?}", msg, l),
      Among::Middle(m) => m,
      Among::Right(r) => panic!("{}: {:?}", msg, r),
    }
  }

  /// Returns the right value
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// let right: Among<(), (), _> = Right(3);
  /// assert_eq!(right.expect_right("value was not Right"), 3);
  /// ```
  ///
  /// # Panics
  ///
  /// When `Among` is a `Left` value
  ///
  /// ```should_panic
  /// # use among::*;
  /// let left: Among<_, (), ()> = Left(3);
  /// left.expect_right("value was not Right");
  /// ```
  ///
  /// When `Among` is a `Middle` value
  ///
  /// ```should_panic
  /// # use among::*;
  /// let middle: Among<(), _, ()> = Middle(3);
  /// middle.expect_right("value was not Right");
  /// ```
  pub fn expect_right(self, msg: &str) -> R
  where
    L: core::fmt::Debug,
    M: core::fmt::Debug,
  {
    match self {
      Among::Right(r) => r,
      Among::Middle(m) => panic!("{}: {:?}", msg, m),
      Among::Left(l) => panic!("{}: {:?}", msg, l),
    }
  }

  /// Convert the contained value into `T`
  ///
  /// # Examples
  ///
  /// ```
  /// # use among::*;
  /// // Both u16 and u32 can be converted to u64.
  /// let left: Among<u16, u32, u64> = Left(3u16);
  /// assert_eq!(left.among_into::<u64>(), 3u64);
  /// let middle: Among<u16, u32, u64> = Middle(3u32);
  /// assert_eq!(middle.among_into::<u64>(), 3u64);
  /// let right: Among<u16, u32, u64> = Right(7u64);
  /// assert_eq!(right.among_into::<u64>(), 7u64);
  /// ```
  pub fn among_into<T>(self) -> T
  where
    L: Into<T>,
    M: Into<T>,
    R: Into<T>,
  {
    match self {
      Among::Left(l) => l.into(),
      Among::Middle(m) => m.into(),
      Among::Right(r) => r.into(),
    }
  }
}

impl<L, M, R> Among<Option<L>, Option<M>, Option<R>> {
  /// Factors out `None` from an `Among` of [`Option`].
  ///
  /// ```
  /// use among::*;
  /// let left: Among<_, Option<u32>, Option<String>> = Left(Some(vec![0]));
  /// assert_eq!(left.factor_none(), Some(Left(vec![0])));
  ///
  /// let right: Among<Option<Vec<u8>>, Option<u32>, _> = Right(Some(String::new()));
  /// assert_eq!(right.factor_none(), Some(Right(String::new())));
  ///
  /// let middle: Among<Option<Vec<u8>>, _, Option<String>> = Middle(Some(123));
  /// assert_eq!(middle.factor_none(), Some(Middle(123)));
  /// ```
  // TODO(MSRV): doc(alias) was stabilized in Rust 1.48
  // #[doc(alias = "transpose")]
  pub fn factor_none(self) -> Option<Among<L, M, R>> {
    match self {
      Left(l) => l.map(Among::Left),
      Middle(m) => m.map(Among::Middle),
      Right(r) => r.map(Among::Right),
    }
  }
}

impl<L, M, R, E> Among<Result<L, E>, Result<M, E>, Result<R, E>> {
  /// Factors out a homogenous type from an `Among` of [`Result`].
  ///
  /// Here, the homogeneous type is the `Err` type of the [`Result`].
  ///
  /// ```
  /// use among::*;
  /// let left: Among<_, Result<u32, u32>, Result<String, u32>> = Left(Ok(vec![0]));
  /// assert_eq!(left.factor_err(), Ok(Left(vec![0])));
  ///
  /// let right: Among<Result<Vec<u8>, u32>, Result<u32, u32>, _> = Right(Ok(String::new()));
  /// assert_eq!(right.factor_err(), Ok(Right(String::new())));
  ///
  /// let middle: Among<Result<Vec<u8>, u32>, _, Result<String, u32>> = Middle(Ok(123));
  /// assert_eq!(middle.factor_err(), Ok(Middle(123)));
  /// ```
  // TODO(MSRV): doc(alias) was stabilized in Rust 1.48
  // #[doc(alias = "transpose")]
  pub fn factor_err(self) -> Result<Among<L, M, R>, E> {
    match self {
      Left(l) => l.map(Among::Left),
      Middle(m) => m.map(Among::Middle),
      Right(r) => r.map(Among::Right),
    }
  }
}

impl<T, L, M, R> Among<Result<T, L>, Result<T, M>, Result<T, R>> {
  /// Factors out a homogenous type from an `Among` of [`Result`].
  ///
  /// Here, the homogeneous type is the `Ok` type of the [`Result`].
  ///
  /// ```
  /// use among::*;
  /// let left: Among<_, Result<u32, i64>, Result<u32, String>> = Left(Err(vec![0]));
  /// assert_eq!(left.factor_ok(), Err(Left(vec![0])));
  ///
  /// let right: Among<Result<u32, Vec<u8>>, Result<u32, i64>, _> = Right(Err(String::new()));
  /// assert_eq!(right.factor_ok(), Err(Right(String::new())));
  ///
  /// let middle: Among<Result<u32, Vec<u8>>, _, Result<u32, String>> = Middle(Err(-123));
  /// assert_eq!(middle.factor_ok(), Err(Middle(-123)));
  /// ```
  // TODO(MSRV): doc(alias) was stabilized in Rust 1.48
  // #[doc(alias = "transpose")]
  pub fn factor_ok(self) -> Result<T, Among<L, M, R>> {
    match self {
      Left(l) => l.map_err(Among::Left),
      Middle(m) => m.map_err(Among::Middle),
      Right(r) => r.map_err(Among::Right),
    }
  }
}

impl<T, L, M, R> Among<(T, L), (T, M), (T, R)> {
  /// Factor out a homogeneous type from an among of pairs.
  ///
  /// Here, the homogeneous type is the first element of the pairs.
  ///
  /// ```
  /// use among::*;
  /// let left: Among<_, (u32, i64), (u32, String)> = Left((123, vec![0]));
  /// assert_eq!(left.factor_first().0, 123);
  ///
  /// let right: Among<(u32, Vec<u8>), (u32, i64), _> = Right((123, String::new()));
  /// assert_eq!(right.factor_first().0, 123);
  ///
  /// let middle: Among<(u32, Vec<u8>), _, (u32, String)> = Middle((123, vec![0]));
  /// assert_eq!(middle.factor_first().0, 123);
  /// ```
  pub fn factor_first(self) -> (T, Among<L, M, R>) {
    match self {
      Left((t, l)) => (t, Left(l)),
      Middle((t, m)) => (t, Middle(m)),
      Right((t, r)) => (t, Right(r)),
    }
  }
}

impl<T, L, M, R> Among<(L, T), (M, T), (R, T)> {
  /// Factor out a homogeneous type from an among of pairs.
  ///
  /// Here, the homogeneous type is the second element of the pairs.
  ///
  /// ```
  /// use among::*;
  /// let left: Among<_, (i64, u32), (String, u32)> = Left((vec![0], 123));
  /// assert_eq!(left.factor_second().1, 123);
  ///
  /// let right: Among<(Vec<u8>, u32), (i64, u32), _> = Right((String::new(), 123));
  /// assert_eq!(right.factor_second().1, 123);
  ///
  /// let middle: Among<(Vec<u8>, u32), _, (String, u32)> = Middle((-1, 123));
  /// assert_eq!(middle.factor_second().1, 123);
  /// ```
  pub fn factor_second(self) -> (Among<L, M, R>, T) {
    match self {
      Left((l, t)) => (Left(l), t),
      Middle((m, t)) => (Middle(m), t),
      Right((r, t)) => (Right(r), t),
    }
  }
}

impl<T> Among<T, T, T> {
  /// Extract the value of an among over two equivalent types.
  ///
  /// ```
  /// use among::*;
  ///
  /// let left: Among<_, _, u32> = Left(123);
  /// assert_eq!(left.into_inner(), 123);
  ///
  /// let right: Among<u32, _, _> = Right(123);
  /// assert_eq!(right.into_inner(), 123);
  ///
  /// let middle: Among<_, u32, _> = Middle(123);
  /// assert_eq!(middle.into_inner(), 123);
  /// ```
  pub fn into_inner(self) -> T {
    for_all!(self, inner => inner)
  }

  /// Map `f` over the contained value and return the result in the
  /// corresponding variant.
  ///
  /// ```
  /// use among::*;
  ///
  /// let value: Among<_, _, i32> = Right(42);
  ///
  /// let other = value.map(|x| x * 2);
  /// assert_eq!(other, Right(84));
  /// ```
  pub fn map<F, M>(self, f: F) -> Among<M, M, M>
  where
    F: FnOnce(T) -> M,
  {
    match self {
      Left(l) => Left(f(l)),
      Middle(m) => Middle(f(m)),
      Right(r) => Right(f(r)),
    }
  }
}

impl<L, M, R> Among<&L, &M, &R> {
  /// Maps an `Among<&L, &M, &R>` to an `Among<L, M, R>` by cloning the contents of
  /// among branch.
  pub fn cloned(self) -> Among<L, M, R>
  where
    L: Clone,
    M: Clone,
    R: Clone,
  {
    match self {
      Self::Left(l) => Among::Left(l.clone()),
      Self::Middle(m) => Among::Middle(m.clone()),
      Self::Right(r) => Among::Right(r.clone()),
    }
  }

  /// Maps an `Among<&L, &M, &R>` to an `Among<L, M, R>` by copying the contents of
  /// among branch.
  pub fn copied(self) -> Among<L, M, R>
  where
    L: Copy,
    M: Copy,
    R: Copy,
  {
    match self {
      Self::Left(l) => Among::Left(*l),
      Self::Middle(m) => Among::Middle(*m),
      Self::Right(r) => Among::Right(*r),
    }
  }
}

impl<L, M, R> Among<&mut L, &mut M, &mut R> {
  /// Maps an `Among<&mut L, &mut M, &mut R>` to an `Among<L, M, R>` by cloning the contents of
  /// among branch.
  pub fn cloned(self) -> Among<L, M, R>
  where
    L: Clone,
    M: Clone,
    R: Clone,
  {
    match self {
      Self::Left(l) => Among::Left(l.clone()),
      Self::Middle(m) => Among::Middle(m.clone()),
      Self::Right(r) => Among::Right(r.clone()),
    }
  }

  /// Maps an `Among<&mut L, &mut M, &mut R>` to an `Among<L, M, R>` by copying the contents of
  /// among branch.
  pub fn copied(self) -> Among<L, M, R>
  where
    L: Copy,
    M: Copy,
    R: Copy,
  {
    match self {
      Self::Left(l) => Among::Left(*l),
      Self::Middle(m) => Among::Middle(*m),
      Self::Right(r) => Among::Right(*r),
    }
  }
}

/// `Among<L, M, R>` is a future if both `L`, `M` and `R` are futures.
impl<L, M, R> Future for Among<L, M, R>
where
  L: Future,
  M: Future,
  R: Future,
{
  type Output = Among<L::Output, M::Output, R::Output>;

  fn poll(
    self: Pin<&mut Self>,
    cx: &mut core::task::Context<'_>,
  ) -> core::task::Poll<Self::Output> {
    match self.as_pin_mut() {
      Left(l) => l.poll(cx).map(Left),
      Middle(m) => m.poll(cx).map(Middle),
      Right(r) => r.poll(cx).map(Right),
    }
  }
}

#[cfg(any(test, feature = "std"))]
/// `Among<L, M, R>` implements `Read` if both `L` and `R` do.
///
/// Requires crate feature `"std"`
impl<L, M, R> Read for Among<L, M, R>
where
  L: Read,
  M: Read,
  R: Read,
{
  fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
    for_all!(*self, ref mut inner => inner.read(buf))
  }

  fn read_exact(&mut self, buf: &mut [u8]) -> io::Result<()> {
    for_all!(*self, ref mut inner => inner.read_exact(buf))
  }

  fn read_to_end(&mut self, buf: &mut std::vec::Vec<u8>) -> io::Result<usize> {
    for_all!(*self, ref mut inner => inner.read_to_end(buf))
  }

  fn read_to_string(&mut self, buf: &mut std::string::String) -> io::Result<usize> {
    for_all!(*self, ref mut inner => inner.read_to_string(buf))
  }
}

#[cfg(any(test, feature = "std"))]
/// `Among<L, M, R>` implements `Seek` if both `L` and `R` do.
///
/// Requires crate feature `"std"`
impl<L, M, R> Seek for Among<L, M, R>
where
  L: Seek,
  M: Seek,
  R: Seek,
{
  fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
    for_all!(*self, ref mut inner => inner.seek(pos))
  }
}

#[cfg(any(test, feature = "std"))]
/// Requires crate feature `"std"`
impl<L, M, R> BufRead for Among<L, M, R>
where
  L: BufRead,
  M: BufRead,
  R: BufRead,
{
  fn fill_buf(&mut self) -> io::Result<&[u8]> {
    for_all!(*self, ref mut inner => inner.fill_buf())
  }

  fn consume(&mut self, amt: usize) {
    for_all!(*self, ref mut inner => inner.consume(amt))
  }

  fn read_until(&mut self, byte: u8, buf: &mut std::vec::Vec<u8>) -> io::Result<usize> {
    for_all!(*self, ref mut inner => inner.read_until(byte, buf))
  }

  fn read_line(&mut self, buf: &mut std::string::String) -> io::Result<usize> {
    for_all!(*self, ref mut inner => inner.read_line(buf))
  }
}

#[cfg(any(test, feature = "std"))]
/// `Among<L, M, R>` implements `Write` if all of `L`, `M` and `R` do.
///
/// Requires crate feature `"std"`
impl<L, M, R> Write for Among<L, M, R>
where
  L: Write,
  M: Write,
  R: Write,
{
  fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
    for_all!(*self, ref mut inner => inner.write(buf))
  }

  fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
    for_all!(*self, ref mut inner => inner.write_all(buf))
  }

  fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> io::Result<()> {
    for_all!(*self, ref mut inner => inner.write_fmt(fmt))
  }

  fn flush(&mut self) -> io::Result<()> {
    for_all!(*self, ref mut inner => inner.flush())
  }
}

impl<L, M, R, Target> AsRef<Target> for Among<L, M, R>
where
  L: AsRef<Target>,
  M: AsRef<Target>,
  R: AsRef<Target>,
{
  fn as_ref(&self) -> &Target {
    for_all!(*self, ref inner => inner.as_ref())
  }
}

macro_rules! impl_specific_ref_and_mut {
    ($t:ty, $($attr:meta),* ) => {
        $(#[$attr])*
        impl<L, M, R> AsRef<$t> for Among<L, M, R>
            where L: AsRef<$t>, M: AsRef<$t>, R: AsRef<$t>,
        {
            fn as_ref(&self) -> &$t {
                for_all!(*self, ref inner => inner.as_ref())
            }
        }

        $(#[$attr])*
        impl<L, M, R> AsMut<$t> for Among<L, M, R>
            where L: AsMut<$t>, M: AsMut<$t>, R: AsMut<$t>,
        {
            fn as_mut(&mut self) -> &mut $t {
                for_all!(*self, ref mut inner => inner.as_mut())
            }
        }
    };
}

impl_specific_ref_and_mut!(str,);
impl_specific_ref_and_mut!(
  ::std::path::Path,
  cfg(feature = "std"),
  doc = "Requires crate feature `std`."
);
impl_specific_ref_and_mut!(
  ::std::ffi::OsStr,
  cfg(feature = "std"),
  doc = "Requires crate feature `std`."
);
impl_specific_ref_and_mut!(
  ::std::ffi::CStr,
  cfg(feature = "std"),
  doc = "Requires crate feature `std`."
);

impl<L, M, R, Target> AsRef<[Target]> for Among<L, M, R>
where
  L: AsRef<[Target]>,
  M: AsRef<[Target]>,
  R: AsRef<[Target]>,
{
  fn as_ref(&self) -> &[Target] {
    for_all!(*self, ref inner => inner.as_ref())
  }
}

impl<L, M, R, Target> AsMut<Target> for Among<L, M, R>
where
  L: AsMut<Target>,
  M: AsMut<Target>,
  R: AsMut<Target>,
{
  fn as_mut(&mut self) -> &mut Target {
    for_all!(*self, ref mut inner => inner.as_mut())
  }
}

impl<L, M, R, Target> AsMut<[Target]> for Among<L, M, R>
where
  L: AsMut<[Target]>,
  M: AsMut<[Target]>,
  R: AsMut<[Target]>,
{
  fn as_mut(&mut self) -> &mut [Target] {
    for_all!(*self, ref mut inner => inner.as_mut())
  }
}

impl<L, M, R> Deref for Among<L, M, R>
where
  L: Deref,
  M: Deref<Target = L::Target>,
  R: Deref<Target = L::Target>,
{
  type Target = L::Target;

  fn deref(&self) -> &Self::Target {
    for_all!(*self, ref inner => &**inner)
  }
}

impl<L, M, R> DerefMut for Among<L, M, R>
where
  L: DerefMut,
  M: DerefMut<Target = L::Target>,
  R: DerefMut<Target = L::Target>,
{
  fn deref_mut(&mut self) -> &mut Self::Target {
    for_all!(*self, ref mut inner => &mut *inner)
  }
}

#[cfg(any(test, feature = "std"))]
/// `Among` implements `Error` if *all* of `L`, `M` and `R` implement it.
///
/// Requires crate feature `"std"`
impl<L, M, R> Error for Among<L, M, R>
where
  L: Error,
  M: Error,
  R: Error,
{
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    for_all!(*self, ref inner => inner.source())
  }

  #[allow(deprecated)]
  fn description(&self) -> &str {
    for_all!(*self, ref inner => inner.description())
  }

  #[allow(deprecated)]
  fn cause(&self) -> Option<&dyn Error> {
    for_all!(*self, ref inner => inner.cause())
  }
}

impl<L, M, R> fmt::Display for Among<L, M, R>
where
  L: fmt::Display,
  M: fmt::Display,
  R: fmt::Display,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for_all!(*self, ref inner => inner.fmt(f))
  }
}

#[test]
fn basic() {
  let mut e = Left(2);
  let m = Middle(2);
  let r = Right(2);
  assert_eq!(e, Left(2));
  e = r;
  assert_eq!(e, Right(2));
  assert_eq!(e.left(), None);
  assert_eq!(e.middle(), None);
  assert_eq!(e.right(), Some(2));
  assert_eq!(e.as_ref().right(), Some(&2));
  assert_eq!(e.as_mut().right(), Some(&mut 2));
  e = m;
  assert_eq!(e, Middle(2));
  assert_eq!(e.left(), None);
  assert_eq!(e.right(), None);
  assert_eq!(e.middle(), Some(2));
  assert_eq!(e.as_ref().middle(), Some(&2));
  assert_eq!(e.as_mut().middle(), Some(&mut 2));
}

#[test]
fn deref() {
  use std::{borrow::Cow, string::String};

  fn is_str(_: &str) {}
  let value: Among<String, Cow<'_, str>, &str> = Left(String::from("test"));
  is_str(&value);
}

#[test]
fn iter() {
  let x = 3;
  let mut iter = match x {
    3 => Left(0..10),
    6 => Middle(11..17),
    _ => Right(17..),
  };

  assert_eq!(iter.next(), Some(0));
  assert_eq!(iter.count(), 9);
}

#[test]
fn seek() {
  use std::{io, vec};

  let use_empty = 1;
  let mut mockdata = [0x00; 256];
  let mut mockvec = vec![];
  for (i, elem) in mockdata.iter_mut().enumerate() {
    mockvec.push(i as u8);
    *elem = i as u8;
  }

  let mut reader = if use_empty == 0 {
    // Empty didn't impl Seek until Rust 1.51
    Left(io::Cursor::new([]))
  } else if use_empty == 1 {
    Right(io::Cursor::new(&mockdata[..]))
  } else {
    Middle(io::Cursor::new(&mockvec[..]))
  };

  let mut buf = [0u8; 16];
  assert_eq!(reader.read(&mut buf).unwrap(), buf.len());
  assert_eq!(buf, mockdata[..buf.len()]);

  // the first read should advance the cursor and return the next 16 bytes thus the `ne`
  assert_eq!(reader.read(&mut buf).unwrap(), buf.len());
  assert_ne!(buf, mockdata[..buf.len()]);

  // if the seek operation fails it should read 16..31 instead of 0..15
  reader.seek(io::SeekFrom::Start(0)).unwrap();
  assert_eq!(reader.read(&mut buf).unwrap(), buf.len());
  assert_eq!(buf, mockdata[..buf.len()]);
}

#[test]
fn read_write() {
  use std::{io, vec};

  let io = 1;
  let mockdata = [0xff; 256];
  let mut mockvec = io::Cursor::new(vec![]);

  let mut reader = if io == 0 {
    Left(io::stdin())
  } else if io == 1 {
    Right(&mockdata[..])
  } else {
    Middle(&mut mockvec)
  };

  let mut buf = [0u8; 16];
  assert_eq!(reader.read(&mut buf).unwrap(), buf.len());
  assert_eq!(&buf, &mockdata[..buf.len()]);

  let mut mockbuf = [0u8; 256];
  let mut writer = if io == 0 {
    Left(io::stdout())
  } else if io == 1 {
    Right(&mut mockbuf[..])
  } else {
    Middle(&mut mockvec)
  };

  let buf = [1u8; 16];
  assert_eq!(writer.write(&buf).unwrap(), buf.len());
}

/// A helper macro to check if AsRef and AsMut are implemented for a given type.
macro_rules! check_t {
  ($t:ty) => {{
    fn check_ref<T: AsRef<$t>>() {}
    fn propagate_ref<T1: AsRef<$t>, T2: AsRef<$t>, T3: AsRef<$t>>() {
      check_ref::<Among<T1, T2, T3>>()
    }
    fn check_mut<T: AsMut<$t>>() {}
    fn propagate_mut<T1: AsMut<$t>, T2: AsMut<$t>, T3: AsMut<$t>>() {
      check_mut::<Among<T1, T2, T3>>()
    }
  }};
}

// This "unused" method is here to ensure that compilation doesn't fail on given types.
fn _unsized_ref_propagation() {
  check_t!(str);

  fn check_array_ref<T: AsRef<[Item]>, Item>() {}
  fn check_array_mut<T: AsMut<[Item]>, Item>() {}

  fn propagate_array_ref<T1: AsRef<[Item]>, T2: AsRef<[Item]>, T3: AsRef<[Item]>, Item>() {
    check_array_ref::<Among<T1, T2, T3>, _>()
  }

  fn propagate_array_mut<T1: AsMut<[Item]>, T2: AsMut<[Item]>, T3: AsMut<[Item]>, Item>() {
    check_array_mut::<Among<T1, T2, T3>, _>()
  }
}

// This "unused" method is here to ensure that compilation doesn't fail on given types.
#[cfg(feature = "std")]
fn _unsized_std_propagation() {
  check_t!(::std::path::Path);
  check_t!(::std::ffi::OsStr);
  check_t!(::std::ffi::CStr);
}
