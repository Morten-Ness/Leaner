import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [PartialOrder α]

variable [LocallyFiniteOrderTop α]

theorem mul_prod_Ioi_eq_prod_Ici (a : α) : f a * ∏ x ∈ Ioi a, f x = ∏ x ∈ Ici a, f x := by
  rw [Ici_eq_cons_Ioi, prod_cons]

