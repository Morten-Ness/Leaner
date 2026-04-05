import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem of_injective : Function.Injective (@FreeMonoid.of α) := List.singleton_injective

