import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem of_smul (f : α → β → β) (x : α) (y : β) :
    (by
      let _ : SMul α β := ⟨f⟩
      exact x • y) = f x y := by
  rfl
