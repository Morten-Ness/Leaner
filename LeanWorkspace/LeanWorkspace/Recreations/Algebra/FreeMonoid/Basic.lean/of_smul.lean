import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem of_smul (f : α → β → β) (x : α) (y : β) :
    (haveI := FreeMonoid.mkMulAction f
    FreeMonoid.of x • y) = f x y := rfl

