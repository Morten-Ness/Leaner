import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem supDegree_eq_natDegree (p : R[X]) : p.toFinsupp.supDegree id = p.natDegree := by
  obtain rfl | h := eq_or_ne p 0
  · simp
  apply WithBot.coe_injective
  rw [← AddMonoidAlgebra.supDegree_withBot_some_comp, Function.comp_id, supDegree_eq_degree,
    degree_eq_natDegree h, Nat.cast_withBot]
  rwa [support_toFinsupp, nonempty_iff_ne_empty, Ne, support_eq_empty]

