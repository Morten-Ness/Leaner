import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeff_ofNat_succ (a n : ℕ) [h : a.AtLeastTwo] :
    Polynomial.coeff (ofNat(a) : R[X]) (n + 1) = 0 := by
  rw [← Nat.cast_ofNat]
  simp [-Nat.cast_ofNat]

