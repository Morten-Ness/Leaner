import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_smul (r : R) : (r • p).map f = f r • p.map f := by
  rw [map, Polynomial.eval₂_smul, RingHom.comp_apply, C_mul']

