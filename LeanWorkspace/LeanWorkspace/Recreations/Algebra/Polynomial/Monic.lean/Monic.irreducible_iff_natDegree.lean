import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [CommSemiring R] {p : R[X]}

variable [NoZeroDivisors R] {p q : R[X]}

theorem Monic.irreducible_iff_natDegree (hp : p.Monic) :
    Irreducible p ↔
      p ≠ 1 ∧ ∀ f g : R[X], f.Monic → g.Monic → f * g = p → f.natDegree = 0 ∨ g.natDegree = 0 := by
  by_cases hp1 : p = 1; · simp [hp1]
  rw [Polynomial.irreducible_of_monic hp hp1, and_iff_right hp1]
  refine forall₄_congr fun a b ha hb => ?_
  rw [ha.natDegree_eq_zero, hb.natDegree_eq_zero]

