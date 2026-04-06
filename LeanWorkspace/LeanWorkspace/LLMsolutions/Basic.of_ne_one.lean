import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem of_ne_one (a : α) : FreeMonoid.of a ≠ 1 := by
  intro h
  have := congrArg FreeMonoid.toList h
  simp [FreeMonoid.toList] at this
