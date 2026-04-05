import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p : R[X]}

variable {p q : R[X]} {ι : Type*}

theorem Monic.ne_zero [Nontrivial R] {p : R[X]} (hp : p.Monic) :
    p ≠ 0 := by
  rintro rfl
  simp [Polynomial.Monic] at hp

