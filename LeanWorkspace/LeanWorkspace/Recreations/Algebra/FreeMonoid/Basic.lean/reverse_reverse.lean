import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem reverse_reverse {a : FreeMonoid α} : FreeMonoid.reverse (FreeMonoid.reverse a) = a := by
  apply List.reverse_reverse

