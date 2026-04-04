import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem direction_sup {s₁ s₂ : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s₁) (hp₂ : p₂ ∈ s₂) :
    (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction ⊔ k ∙ (p₂ -ᵥ p₁) := by
  refine le_antisymm ?_ ?_
  · change (affineSpan k ((s₁ : Set P) ∪ s₂)).direction ≤ _
    rw [← mem_coe] at hp₁
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right k (Set.mem_union_left _ hp₁),
      Submodule.span_le]
    rintro v ⟨p₃, hp₃, rfl⟩
    rcases hp₃ with hp₃ | hp₃
    · rw [sup_assoc, sup_comm, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p₃ -ᵥ p₁, vsub_mem_direction hp₃ hp₁
      rw [zero_add]
    · rw [sup_assoc, SetLike.mem_coe, Submodule.mem_sup]
      use 0, Submodule.zero_mem _, p₃ -ᵥ p₁
      rw [and_comm, zero_add]
      use rfl
      rw [← vsub_add_vsub_cancel p₃ p₂ p₁, Submodule.mem_sup]
      use p₃ -ᵥ p₂, vsub_mem_direction hp₃ hp₂, p₂ -ᵥ p₁, Submodule.mem_span_singleton_self _
  · refine sup_le (sup_direction_le _ _) ?_
    rw [direction_eq_vectorSpan, vectorSpan_def]
    exact
      sInf_le_sInf fun p hp =>
        Set.Subset.trans
          (Set.singleton_subset_iff.2
            (vsub_mem_vsub (mem_affineSpan k (Set.mem_union_right _ hp₂))
              (mem_affineSpan k (Set.mem_union_left _ hp₁))))
          hp

