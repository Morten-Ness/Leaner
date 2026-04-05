import Mathlib

variable {M : Type*}

theorem coe_closure' [Monoid M] {s : Set M} :
    (closure s : Set M) = Set.univ * s := by
  rw [SemigroupIdeal.coe_closure, union_eq_right]
  exact fun x hx => ⟨1, mem_univ 1, x, hx, by simp⟩

