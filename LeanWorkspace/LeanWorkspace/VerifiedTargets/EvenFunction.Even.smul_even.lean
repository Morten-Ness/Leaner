import Mathlib

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Even.smul_even [SMul β γ] (hf : f.Even) (hg : g.Even) : (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a]

