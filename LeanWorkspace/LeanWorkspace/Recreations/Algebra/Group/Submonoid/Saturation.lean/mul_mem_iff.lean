import Mathlib

variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

include h in
theorem mul_mem_iff {x y : M} : x * y ∈ s ↔ x ∈ s ∧ y ∈ s := ⟨@h _ _, and_imp.mpr mul_mem⟩

