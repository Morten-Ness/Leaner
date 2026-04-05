import Mathlib

variable {α β : Type*} [Neg α]

theorem Even.add [Add β] {f g : α → β} (hf : f.Even) (hg : g.Even) : (f + g).Even := by
  intro a
  simp only [hf a, hg a, Pi.add_apply]

