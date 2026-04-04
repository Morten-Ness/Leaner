import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable (k) in

theorem vectorSpan_union_of_mem_of_mem {s₁ s₂ : Set P} {p : P} (hp₁ : p ∈ s₁) (hp₂ : p ∈ s₂) :
    vectorSpan k (s₁ ∪ s₂) = vectorSpan k s₁ ⊔ vectorSpan k s₂ := by
  simp_rw [← direction_affineSpan, span_union,
    AffineSubspace.direction_sup_eq_sup_direction (mem_affineSpan k hp₁) (mem_affineSpan k hp₂)]

