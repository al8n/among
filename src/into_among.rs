//! The trait [`IntoAmong`] provides methods for converting a type `Self`, whose
//! size is constant and known at compile-time, into an [`Among`] variant.

use super::{Among, Left, Middle, Right};

/// Provides methods for converting a type `Self` into among a [`Left`] [`Middle`] or [`Right`]
/// variant of [`Among<Self, Self>`](Among).
///
/// The [`into_among`](IntoAmong::into_among) method takes a [`bool`] to determine
/// whether to convert to [`Left`] or [`Right`].
///
/// The [`into_among_with`](IntoAmong::into_among_with) method takes a
/// [predicate function](FnOnce) to determine whether to convert to [`Left`] [`Middle`] or [`Right`].
pub trait IntoAmong: Sized {
  /// Converts `self` into a [`Left`] variant of [`Among<Self, Self>`](Among)
  /// if `into_left` is `Some(true)`.
  ///
  /// Converts `self` into a [`Middle`] variant of [`Among<Self, Self>`](Among)
  /// if `into_left` is `None`.
  ///
  /// Converts `self` into a [`Right`] variant of [`Among<Self, Self>`](Among)
  /// if `into_left` is `Some(false)`.
  ///
  /// # Examples
  ///
  /// ```
  /// use among::{IntoAmong, Left, Right, Middle};
  ///
  /// let x = 0;
  /// assert_eq!(x.into_among(Some(true)), Left(x));
  /// assert_eq!(x.into_among(Some(false)), Right(x));
  /// assert_eq!(x.into_among(None), Middle(x));
  /// ```
  fn into_among(self, into_left: Option<bool>) -> Among<Self, Self, Self> {
    match into_left {
      Some(into_left) => {
        if into_left {
          Left(self)
        } else {
          Right(self)
        }
      }
      None => Middle(self),
    }
  }

  /// Converts `self` into a [`Left`] variant of [`Among<Self, Self>`](Among)
  /// if `into_left(&self)` returns `Some(true)`.
  ///
  /// Converts `self` into a [`Middle`] variant of [`Among<Self, Self>`](Among)
  /// if `into_left(&self)` returns `None`.
  ///
  /// Converts `self` into a [`Right`] variant of [`Among<Self, Self>`](Among)
  /// if `into_left(&self)` returns `Some(false)`.
  ///
  /// # Examples
  ///
  /// ```
  /// use among::{IntoAmong, Left, Right, Middle};
  ///
  /// fn is(x: &u8) -> Option<bool> {
  ///     if x % 3 == 0 {
  ///         None
  ///     } else if x % 3 == 1 {
  ///         Some(true)
  ///     } else {
  ///         Some(false)
  ///     }
  /// }
  ///
  /// let x = 0;
  /// assert_eq!(x.into_among_with(is), Middle(x));
  ///
  /// let x = 1;
  /// assert_eq!(x.into_among_with(is), Left(x));
  ///
  /// let x = 2;
  /// assert_eq!(x.into_among_with(is), Right(x));
  /// ```
  fn into_among_with<F>(self, into_left: F) -> Among<Self, Self, Self>
  where
    F: FnOnce(&Self) -> Option<bool>,
  {
    let into_left = into_left(&self);
    self.into_among(into_left)
  }
}

impl<T> IntoAmong for T {}
