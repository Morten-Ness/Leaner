import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem toList_mul (xs ys : FreeMonoid α) : FreeMonoid.toList (xs * ys) = FreeMonoid.toList xs ++ FreeMonoid.toList ys := rfl

