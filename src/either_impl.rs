use either::Either;

use super::Among;

impl<L, R, M> From<Either<L, R>> for Among<L, M, R> {
  fn from(either: Either<L, R>) -> Among<L, M, R> {
    match either {
      Either::Left(left) => Among::Left(left),
      Either::Right(right) => Among::Right(right),
    }
  }
}

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
