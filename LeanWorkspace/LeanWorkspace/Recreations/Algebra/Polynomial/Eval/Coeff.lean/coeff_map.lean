import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) := by
  rw [map, eval₂_def, coeff_sum, sum]
  simp_all

