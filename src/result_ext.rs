use super::Among;

/// An extension trait for `Result<_, Among<A, B, C>>` that provides additional methods.
pub trait AmongErrorExt<T, L, M, R> {
  /// Apply the function `f` on the value in the `Left` variant if it is present rewrapping the
  /// result in `Left`.
  fn map_err_left<F, N>(self, l: F) -> Result<T, Among<N, M, R>>
  where
    F: FnOnce(L) -> N;

  /// Apply the function `f` on the value in the `Middle` variant if it is present rewrapping the
  /// result in `Middle`.
  fn map_err_middle<F, N>(self, m: F) -> Result<T, Among<L, N, R>>
  where
    F: FnOnce(M) -> N;

  /// Apply the function `f` on the value in the `Right` variant if it is present rewrapping the
  /// result in `Right`.
  fn map_err_right<F, N>(self, r: F) -> Result<T, Among<L, M, N>>
  where
    F: FnOnce(R) -> N;
}

impl<T, L, M, R> AmongErrorExt<T, L, M, R> for Result<T, Among<L, M, R>> {
  #[inline]
  fn map_err_left<F, N>(self, f: F) -> Result<T, Among<N, M, R>>
  where
    F: FnOnce(L) -> N,
  {
    self.map_err(|a| a.map_left(f))
  }

  #[inline]
  fn map_err_middle<F, N>(self, f: F) -> Result<T, Among<L, N, R>>
  where
    F: FnOnce(M) -> N,
  {
    self.map_err(|a| a.map_middle(f))
  }

  #[inline]
  fn map_err_right<F, N>(self, f: F) -> Result<T, Among<L, M, N>>
  where
    F: FnOnce(R) -> N,
  {
    self.map_err(|a| a.map_right(f))
  }
}

/// An extension trait for `Result<Among<A, B, C>, _>` that provides additional methods.
pub trait AmongOkExt<E, L, M, R> {
  /// Apply the function `f` on the value in the `Left` variant if it is present rewrapping the
  /// result in `Left`.
  fn map_left<F, N>(self, l: F) -> Result<Among<N, M, R>, E>
  where
    F: FnOnce(L) -> N;

  /// Apply the function `f` on the value in the `Middle` variant if it is present rewrapping the
  /// result in `Middle`.
  fn map_middle<F, N>(self, m: F) -> Result<Among<L, N, R>, E>
  where
    F: FnOnce(M) -> N;

  /// Apply the function `f` on the value in the `Right` variant if it is present rewrapping the
  /// result in `Right`.
  fn map_right<F, N>(self, r: F) -> Result<Among<L, M, N>, E>
  where
    F: FnOnce(R) -> N;
}

impl<E, L, M, R> AmongOkExt<E, L, M, R> for Result<Among<L, M, R>, E> {
  #[inline]
  fn map_left<F, N>(self, f: F) -> Result<Among<N, M, R>, E>
  where
    F: FnOnce(L) -> N,
  {
    self.map(|a| a.map_left(f))
  }

  #[inline]
  fn map_middle<F, N>(self, f: F) -> Result<Among<L, N, R>, E>
  where
    F: FnOnce(M) -> N,
  {
    self.map(|a| a.map_middle(f))
  }

  #[inline]
  fn map_right<F, N>(self, f: F) -> Result<Among<L, M, N>, E>
  where
    F: FnOnce(R) -> N,
  {
    self.map(|a| a.map_right(f))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_ext() {
    let result: Result<Among<u64, u64, u64>, Among<&str, &str, &str>> = Err(Among::Left("error"));
    let result = result.map_err_left(|s| s.len());
    assert_eq!(result, Err(Among::Left(5)));

    let result: Result<Among<u64, u64, u64>, Among<&str, &str, &str>> = Ok(Among::Middle(42));
    let result = result.map_middle(|s| s as u128);
    assert_eq!(result, Ok(Among::Middle(42)));
  }
}
