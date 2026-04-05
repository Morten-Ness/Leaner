import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem natDegree_iterate_derivative (p : R[X]) (k : ℕ) :
    (Polynomial.derivative^[k] p).natDegree ≤ p.natDegree - k := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, Nat.sub_zero]
  | succ d hd =>
      rw [Function.iterate_succ_apply', Nat.sub_succ']
      exact (Polynomial.natDegree_derivative_le _).trans <| Nat.sub_le_sub_right hd 1

