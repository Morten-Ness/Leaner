import Mathlib

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

theorem iInf {ι : Sort*} {f : ι → Submonoid M} (hf : ∀ i, (f i).MulSaturated) :
    (iInf f).MulSaturated := Submonoid.MulSaturated.sInf <| Set.forall_mem_range.mpr hf

