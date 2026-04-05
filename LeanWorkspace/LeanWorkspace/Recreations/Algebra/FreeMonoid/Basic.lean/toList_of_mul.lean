import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem toList_of_mul (x : α) (xs : FreeMonoid α) : FreeMonoid.toList (FreeMonoid.of x * xs) = x :: FreeMonoid.toList xs := rfl

