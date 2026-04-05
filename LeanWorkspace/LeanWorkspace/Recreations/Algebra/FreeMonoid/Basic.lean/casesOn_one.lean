import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem casesOn_one {C : FreeMonoid α → Sort*} (h0 : C 1) (ih : ∀ x xs, C (FreeMonoid.of x * xs)) :
    @FreeMonoid.casesOn α C 1 h0 ih = h0 := rfl

