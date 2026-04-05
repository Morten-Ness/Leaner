import Mathlib

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Even.const_smul [SMul β γ] (hg : g.Even) (r : β) : (r • g).Even := by
  intro a
  simp only [Pi.smul_apply, hg a]

