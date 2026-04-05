import Mathlib

variable {α β : Type*} [Neg α]

theorem Odd.add [SubtractionCommMonoid β] {f g : α → β} (hf : f.Odd) (hg : g.Odd) : (f + g).Odd := by
  intro a
  simp only [hf a, hg a, Pi.add_apply, neg_add]

