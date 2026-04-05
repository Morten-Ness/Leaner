import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_eq_zero {p : R[X]} {x : ℕ} (hx : p.natDegree < x) :
    Polynomial.derivative^[x] p = 0 := by
  induction h : p.natDegree using Nat.strong_induction_on generalizing p x with | _ _ ih
  subst h
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (pos_of_gt hx).ne'
  rw [Function.iterate_succ_apply]
  by_cases hp : p.natDegree = 0
  · rw [Polynomial.derivative_of_natDegree_zero hp, Polynomial.iterate_derivative_zero]
  have := Polynomial.natDegree_derivative_lt hp
  exact ih _ this (this.trans_le <| Nat.le_of_lt_succ hx) rfl

