import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem X_sub_C_dvd_sub_C_eval : Polynomial.X - Polynomial.C a ∣ p - Polynomial.C (p.eval a) := by
  rw [Polynomial.dvd_iff_isRoot, IsRoot, eval_sub, eval_C, sub_self]

-- TODO: generalize this to Ring. In general, 0 can be replaced by any element in the center of R.

