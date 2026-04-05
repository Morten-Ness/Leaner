import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem recOn_of_mul {C : FreeMonoid α → Sort*} (x : α) (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C xs → C (FreeMonoid.of x * xs)) : @FreeMonoid.recOn α C (FreeMonoid.of x * xs) h0 ih = ih x xs (FreeMonoid.recOn xs h0 ih) := rfl

