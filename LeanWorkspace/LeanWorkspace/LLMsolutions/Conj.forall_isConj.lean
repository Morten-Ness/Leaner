import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem forall_isConj {p : ConjClasses α → Prop} : (∀ a, p a) ↔ ∀ a, p (ConjClasses.mk a) := by
  constructor
  · intro h a
    exact h (ConjClasses.mk a)
  · intro h a
    rcases Quotient.exists_rep a with ⟨x, rfl⟩
    exact h x
