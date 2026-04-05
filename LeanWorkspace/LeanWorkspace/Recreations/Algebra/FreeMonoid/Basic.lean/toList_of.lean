import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem toList_of (x : α) : FreeMonoid.toList (FreeMonoid.of x) = [x] := rfl

