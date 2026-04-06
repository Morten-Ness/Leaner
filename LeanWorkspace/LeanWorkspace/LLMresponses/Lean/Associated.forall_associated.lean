import Mathlib

variable {M : Type*}

theorem forall_associated [Monoid M] {p : Associates M → Prop} :
    (∀ a, p a) ↔ ∀ a, p (Associates.mk a) := by
  constructor
  · intro h a
    exact h (Associates.mk a)
  · intro h a
    refine Quotient.inductionOn a ?_
    intro b
    exact h b
