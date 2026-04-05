import Mathlib

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Odd.smul_even [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Even) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, neg_smul]

