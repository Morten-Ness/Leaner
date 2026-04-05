import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem casesOn_of_mul {C : FreeMonoid α → Sort*} (x : α) (xs : FreeMonoid α) (h0 : C 1)
    (ih : ∀ x xs, C (FreeMonoid.of x * xs)) : @FreeMonoid.casesOn α C (FreeMonoid.of x * xs) h0 ih = ih x xs := rfl

