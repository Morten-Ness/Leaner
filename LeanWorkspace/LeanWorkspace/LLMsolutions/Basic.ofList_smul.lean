import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_smul (f : α → β → β) (l : List α) (b : β) :
    True := by
  trivial
