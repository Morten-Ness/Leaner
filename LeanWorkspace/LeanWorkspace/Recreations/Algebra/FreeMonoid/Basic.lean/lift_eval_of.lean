import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem lift_eval_of (f : α → M) (x : α) : FreeMonoid.lift f (FreeMonoid.of x) = f x := rfl

