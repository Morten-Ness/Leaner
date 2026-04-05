import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Ring R] {p : R[X]}

theorem Monic.comp_X_sub_C {p : R[X]} (hp : p.Monic) (r : R) : (Polynomial.Monic.comp p (Polynomial.X - Polynomial.C r)).Monic := by
  simpa using Polynomial.Monic.comp_X_add_C hp (-r)

