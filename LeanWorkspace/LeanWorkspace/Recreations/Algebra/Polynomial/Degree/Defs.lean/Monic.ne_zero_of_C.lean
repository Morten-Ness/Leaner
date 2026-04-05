import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem Monic.ne_zero_of_C [Nontrivial R] {c : R} (hc : Polynomial.Monic (Polynomial.C c)) : c ≠ 0 := by
  rintro rfl
  simp [Polynomial.Monic] at hc

