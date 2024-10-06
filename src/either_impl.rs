use either::Either;

use super::Among;

impl<L, M, R> Among<L, M, R> {
  /// Try to convert the `Among` to `Either<L, M>`. If the `Among` is `Right`, it will return an error.
  ///
  /// See also [`into_left_middle`].
  ///
  /// # Examples
  ///
  /// ```rust
  /// use either::Either;
  /// use among::Among;
  ///
  /// let among: Among<i32, (), ()> = Among::Left(1);
  /// let either = among.try_into_left_middle().unwrap();
  ///
  /// assert_eq!(either, Either::Left(1));
  ///
  /// let among: Among<(), i32, ()> = Among::Middle(2);
  /// let either = among.try_into_left_middle().unwrap();
  ///
  /// assert_eq!(either, Either::Right(2));
  /// ```
  #[inline]
  pub fn try_into_left_middle(self) -> Result<Either<L, M>, R> {
    match self {
      Among::Left(left) => Ok(Either::Left(left)),
      Among::Middle(middle) => Ok(Either::Right(middle)),
      Among::Right(right) => Err(right),
    }
  }

  /// Attempts to convert the `Among` to `Either<L, M>`. If the `Among` is `Right`, it will panic.
  ///
  /// See also [`try_into_left_middle`].
  ///
  /// # Examples
  ///
  /// ```rust
  /// use either::Either;
  /// use among::Among;
  ///
  /// let among: Among<i32, (), ()> = Among::Left(1);
  ///
  /// let either = among.into_left_middle();
  ///
  /// assert_eq!(either, Either::Left(1));
  ///
  /// let among: Among<(), i32, ()> = Among::Middle(2);
  ///
  /// let either = among.into_left_middle();
  ///
  /// assert_eq!(either, Either::Right(2));
  /// ```
  #[inline]
  pub fn into_left_middle(self) -> Either<L, M> {
    match self {
      Among::Left(left) => Either::Left(left),
      Among::Middle(middle) => Either::Right(middle),
      Among::Right(_) => panic!("unexpected Among::Right"),
    }
  }

  /// Try to convert the `Among` to `Either<M, R>`. If the `Among` is `Left`, it will return an error.
  ///
  /// See also [`into_middle_right`].
  ///
  /// # Examples
  ///
  /// ```rust
  /// use either::Either;
  /// use among::Among;
  ///
  /// let among: Among<(), i32, ()> = Among::Middle(2);
  /// let either = among.try_into_middle_right().unwrap();
  ///
  /// assert_eq!(either, Either::Left(2));
  ///
  /// let among: Among<(), (), i32> = Among::Right(3);
  /// let either = among.try_into_middle_right().unwrap();
  ///
  /// assert_eq!(either, Either::Right(3));
  /// ```
  #[inline]
  pub fn try_into_middle_right(self) -> Result<Either<M, R>, L> {
    match self {
      Among::Left(left) => Err(left),
      Among::Middle(middle) => Ok(Either::Left(middle)),
      Among::Right(right) => Ok(Either::Right(right)),
    }
  }

  /// Attempts to convert the `Among` to `Either<M, R>`. If the `Among` is `Left`, it will panic.
  ///
  /// See also [`try_into_middle_right`].
  ///
  /// # Examples
  ///
  /// ```rust
  /// use either::Either;
  /// use among::Among;
  ///
  /// let among: Among<(), i32, ()> = Among::Middle(2);
  ///
  /// let either = among.into_middle_right();
  ///
  /// assert_eq!(either, Either::Left(2));
  ///
  /// let among: Among<(), (), i32> = Among::Right(3);
  ///
  /// let either = among.into_middle_right();
  ///
  /// assert_eq!(either, Either::Right(3));
  /// ```
  #[inline]
  pub fn into_middle_right(self) -> Either<M, R> {
    match self {
      Among::Left(_) => panic!("unexpected Among::Left"),
      Among::Middle(middle) => Either::Left(middle),
      Among::Right(right) => Either::Right(right),
    }
  }

  /// Try to convert the `Among` to `Either<L, R>`. If the `Among` is `Middle`, it will return an error.
  ///
  /// See also [`into_left_right`].
  ///
  /// # Examples
  ///
  /// ```rust
  /// use either::Either;
  /// use among::Among;
  ///
  ///
  /// let among: Among<i32, (), i32> = Among::Left(1);
  /// let either = among.try_into_left_right().unwrap();
  ///
  /// assert_eq!(either, Either::Left(1));
  ///
  /// let among: Among<(), i32, i32> = Among::Right(3);
  ///
  /// let either = among.try_into_left_right().unwrap();
  ///
  /// assert_eq!(either, Either::Right(3));
  /// ```
  #[inline]
  pub fn try_into_left_right(self) -> Result<Either<L, R>, M> {
    match self {
      Among::Left(left) => Ok(Either::Left(left)),
      Among::Middle(middle) => Err(middle),
      Among::Right(right) => Ok(Either::Right(right)),
    }
  }

  /// Attempts to convert the `Among` to `Either<L, R>`. If the `Among` is `Middle`, it will panic.
  ///
  /// See also [`try_into_left_right`].
  ///
  /// # Examples
  ///
  /// ```rust
  /// use either::Either;
  /// use among::Among;
  ///
  /// let among: Among<i32, (), i32> = Among::Left(1);
  ///
  /// let either = among.into_left_right();
  ///
  /// assert_eq!(either, Either::Left(1));
  ///
  /// let among: Among<(), i32, i32> = Among::Right(3);
  ///
  /// let either = among.into_left_right();
  ///
  /// assert_eq!(either, Either::Right(3));
  ///
  /// ```
  #[inline]
  pub fn into_left_right(self) -> Either<L, R> {
    match self {
      Among::Left(left) => Either::Left(left),
      Among::Middle(_) => panic!("unexpected Among::Middle"),
      Among::Right(right) => Either::Right(right),
    }
  }
}

impl<A, B, C> From<Either<Either<A, B>, C>> for Among<A, B, C> {
  #[inline]
  fn from(either: Either<Either<A, B>, C>) -> Among<A, B, C> {
    match either {
      Either::Left(Either::Left(a)) => Among::Left(a),
      Either::Left(Either::Right(b)) => Among::Middle(b),
      Either::Right(c) => Among::Right(c),
    }
  }
}

impl<A, B, C> From<Either<A, Either<B, C>>> for Among<A, B, C> {
  #[inline]
  fn from(either: Either<A, Either<B, C>>) -> Among<A, B, C> {
    match either {
      Either::Left(a) => Among::Left(a),
      Either::Right(Either::Left(b)) => Among::Middle(b),
      Either::Right(Either::Right(c)) => Among::Right(c),
    }
  }
}

impl<A, B, C> From<Either<A, B>> for Among<A, B, C> {
  #[inline]
  fn from(either: Either<A, B>) -> Among<A, B, C> {
    match either {
      Either::Left(a) => Among::Left(a),
      Either::Right(b) => Among::Middle(b),
    }
  }
}

/// An extension trait for `Result<Either<A, B>, _>` that provides additional methods.
pub trait EitherOkExt<E, A, B> {
  /// Apply the function `f` on the value in the `Left` variant if it is present rewrapping the
  /// result in `Left`.
  fn map_left<F, U>(self, f: F) -> Result<Either<U, B>, E>
  where
    F: FnOnce(A) -> U;

  /// Apply the function `f` on the value in the `Right` variant if it is present rewrapping the
  /// result in `Right`.
  fn map_right<F, U>(self, f: F) -> Result<Either<A, U>, E>
  where
    F: FnOnce(B) -> U;
}

impl<E, A, B> EitherOkExt<E, A, B> for Result<Either<A, B>, E> {
  #[inline]
  fn map_left<F, U>(self, f: F) -> Result<Either<U, B>, E>
  where
    F: FnOnce(A) -> U,
  {
    self.map(|either| either.map_left(f))
  }

  #[inline]
  fn map_right<F, U>(self, f: F) -> Result<Either<A, U>, E>
  where
    F: FnOnce(B) -> U,
  {
    self.map(|either| either.map_right(f))
  }
}

/// An extension trait for `Result<T, Either<A, B>>` that provides additional methods.
pub trait EitherErrExt<T, A, B> {
  /// Apply the function `f` on the value in the `Left` variant if it is present rewrapping the
  /// result in `Left`.
  fn map_err_left<F, U>(self, f: F) -> Result<T, Either<U, B>>
  where
    F: FnOnce(A) -> U;

  /// Apply the function `f` on the value in the `Right` variant if it is present rewrapping the
  /// result in `Right`.
  fn map_err_right<F, U>(self, f: F) -> Result<T, Either<A, U>>
  where
    F: FnOnce(B) -> U;
}

impl<T, A, B> EitherErrExt<T, A, B> for Result<T, Either<A, B>> {
  #[inline]
  fn map_err_left<F, U>(self, f: F) -> Result<T, Either<U, B>>
  where
    F: FnOnce(A) -> U,
  {
    self.map_err(|either| either.map_left(f))
  }

  #[inline]
  fn map_err_right<F, U>(self, f: F) -> Result<T, Either<A, U>>
  where
    F: FnOnce(B) -> U,
  {
    self.map_err(|either| either.map_right(f))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_ext() {
    let result: Result<Either<u64, u64>, Either<&str, &str>> = Err(Either::Left("error"));
    let result = result.map_err_left(|s| s.len());
    assert_eq!(result, Err(Either::Left(5)));

    let result: Result<Either<u64, u64>, Either<&str, &str>> = Ok(Either::Right(42));
    let result = result.map_right(|s| s as u128);
    assert_eq!(result, Ok(Either::Right(42)));
  }
}
