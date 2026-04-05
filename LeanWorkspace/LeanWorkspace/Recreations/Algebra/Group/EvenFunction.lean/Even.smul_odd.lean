import Mathlib

variable {α β : Type*} [Neg α]

variable {γ : Type*} {f : α → β} {g : α → γ}

theorem Even.smul_odd [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hf : f.Even) (hg : g.Odd) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg]

