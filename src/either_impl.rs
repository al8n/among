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
