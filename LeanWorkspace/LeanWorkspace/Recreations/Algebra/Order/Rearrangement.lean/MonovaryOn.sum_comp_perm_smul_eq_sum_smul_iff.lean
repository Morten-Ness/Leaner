import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

theorem MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f (σ i) • g i = ∑ i ∈ s, f i • g i ↔ MonovaryOn (f ∘ σ) g s := by
  have hσinv : { x | σ⁻¹ x ≠ x } ⊆ s := (set_support_symm_eq _).subset.trans hσ
  refine (Iff.trans ?_ <| hfg.sum_smul_comp_perm_eq_sum_smul_iff hσinv).trans
    ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply eq_iff_eq_cancel_right.2
    rw [σ.sum_comp' s (fun i j ↦ f i • g j) hσ]
    congr
  · convert h.comp_right σ
    · rw [comp_assoc, inv_def, symm_comp_self, comp_id]
    · rw [σ.eq_preimage_iff_image_eq, Set.image_perm hσ]
  · convert h.comp_right σ.symm
    · rw [comp_assoc, self_comp_symm, comp_id]
    · rw [σ.symm.eq_preimage_iff_image_eq]
      exact Set.image_perm hσinv

