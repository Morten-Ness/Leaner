import Mathlib

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Odd.smul_odd [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Odd) :
    (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg, neg_smul, neg_neg]

