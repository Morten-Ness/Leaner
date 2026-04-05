import Mathlib

variable {α β : Type*} [Neg α]

variable {γ : Type*}

theorem Even.comp_odd [Neg β] {f : β → γ} (hf : f.Even) {g : α → β} (hg : g.Odd) :
    (f ∘ g).Even := by
  intro a
  simp only [comp_apply, hg a, hf _]

