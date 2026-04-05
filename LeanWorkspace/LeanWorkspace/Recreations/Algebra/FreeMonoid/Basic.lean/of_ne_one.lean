import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem of_ne_one (a : α) : FreeMonoid.of a ≠ 1 := by
  intro h
  have := congrArg FreeMonoid.length h
  simp only [FreeMonoid.length_of, FreeMonoid.length_one, Nat.succ_ne_self] at this

