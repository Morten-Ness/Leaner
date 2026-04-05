import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulStrictMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

theorem MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i ∈ s, f i • g (σ i) = ∑ i ∈ s, f i • g i ↔ MonovaryOn f (g ∘ σ) s := by
  classical
  refine ⟨not_imp_not.1 fun h ↦ ?_, fun h ↦ (hfg.sum_smul_comp_perm_le_sum_smul hσ).antisymm <| by
    simpa using h.sum_smul_comp_perm_le_sum_smul ((set_support_symm_eq _).subset.trans hσ)⟩
  rw [MonovaryOn] at h
  push Not at h
  obtain ⟨x, hx, y, hy, hgxy, hfxy⟩ := h
  set τ : Equiv.Perm ι := (Equiv.swap x y).trans σ
  have hτs : {x | τ x ≠ x} ⊆ s := by
    refine (set_support_mul_subset σ <| swap x y).trans (Set.union_subset hσ fun z hz ↦ ?_)
    obtain ⟨_, rfl | rfl⟩ := swap_apply_ne_self_iff.1 hz <;> assumption
  refine ((hfg.sum_smul_comp_perm_le_sum_smul hτs).trans_lt' ?_).ne
  obtain rfl | hxy := eq_or_ne x y
  · cases lt_irrefl _ hfxy
  simp only [τ, ← s.sum_erase_add _ hx,
    ← (s.erase x).sum_erase_add _ (mem_erase.2 ⟨hxy.symm, hy⟩),
    add_assoc, Equiv.coe_trans, Function.comp_apply, swap_apply_right, swap_apply_left]
  refine add_lt_add_of_le_of_lt (Finset.sum_congr rfl fun z hz ↦ ?_).le
    (smul_add_smul_lt_smul_add_smul hfxy hgxy)
  simp_rw [mem_erase] at hz
  rw [swap_apply_of_ne_of_ne hz.2.1 hz.1]

