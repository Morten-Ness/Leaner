import Mathlib

open scoped ArithmeticFunction

theorem image_piFinTwoEquiv_finMulAntidiag {n : ℕ} :
    (Nat.finMulAntidiag 2 n).image (piFinTwoEquiv <| fun _ => ℕ) = divisorsAntidiagonal n := by
  ext x
  simp [(piFinTwoEquiv <| fun _ => ℕ).symm.surjective.exists]

