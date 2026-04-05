import Mathlib

variable {M : Type*}

theorem forall_associated [Monoid M] {p : Associates M → Prop} :
    (∀ a, p a) ↔ ∀ a, p (Associates.mk a) := Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

