import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem spanPoints_subset_coe_of_subset_coe {s : Set P} {s₁ : AffineSubspace k P} (h : s ⊆ s₁) :
    spanPoints k s ⊆ s₁ := by
  rintro p ⟨p₁, hp₁, v, hv, hp⟩
  rw [hp]
  have hp₁s₁ : p₁ ∈ (s₁ : Set P) := Set.mem_of_mem_of_subset hp₁ h
  refine AffineSubspace.vadd_mem_of_mem_direction ?_ hp₁s₁
  have hs : vectorSpan k s ≤ s₁.direction := vectorSpan_mono k h
  rw [SetLike.le_def] at hs
  rw [← SetLike.mem_coe]
  exact Set.mem_of_mem_of_subset hv hs

