import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem smul_def (f : α → β → β) (l : FreeMonoid α) (b : β) :
    haveI := FreeMonoid.mkMulAction f
    l • b = l.toList.foldr f b := rfl

