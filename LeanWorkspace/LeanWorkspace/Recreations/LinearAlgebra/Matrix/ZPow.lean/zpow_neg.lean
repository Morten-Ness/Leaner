import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem zpow_neg {A : M} (h : IsUnit A.det) : ∀ n : ℤ, A ^ (-n) = (A ^ n)⁻¹
  | (n : ℕ) => Matrix.zpow_neg_natCast _ _
  | -[n+1] => by
    rw [zpow_negSucc, neg_negSucc, zpow_natCast, nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _
