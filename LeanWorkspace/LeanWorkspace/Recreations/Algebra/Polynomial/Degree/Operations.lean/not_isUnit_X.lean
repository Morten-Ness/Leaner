import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Nontrivial R] {p q : R[X]} (n : ℕ)

theorem not_isUnit_X : ¬IsUnit (Polynomial.X : R[X]) := fun ⟨⟨_, g, _hfg, hgf⟩, rfl⟩ =>
  zero_ne_one' R <| by
    rw [← coeff_one_zero, ← hgf]
    simp

