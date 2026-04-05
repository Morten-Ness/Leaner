import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem toList_prod (xs : List (FreeMonoid α)) : FreeMonoid.toList xs.prod = (xs.map FreeMonoid.toList).flatten := by
  induction xs <;> simp [*]

