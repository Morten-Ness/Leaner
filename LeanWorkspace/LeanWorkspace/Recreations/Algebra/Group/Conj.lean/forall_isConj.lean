import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem forall_isConj {p : ConjClasses α → Prop} : (∀ a, p a) ↔ ∀ a, p (ConjClasses.mk a) := Iff.intro (fun h _ => h _) fun h a => Quotient.inductionOn a h

