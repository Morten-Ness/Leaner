import Mathlib

variable {ι α β : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]
  [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β] [Module α β]

variable [PosSMulMono α β] {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

theorem MonovaryOn.sum_smul_comp_perm_le_sum_smul (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i ∈ s, f i • g (σ i) ≤ ∑ i ∈ s, f i • g i := by
  classical
  induction s using induction_on_max_value fun i ↦ toLex (g i, f i) generalizing σ with
  | empty => simp only [le_rfl, Finset.sum_empty]
  | insert a s has hamax hind => ?_
  set τ : Equiv.Perm ι := σ.trans (swap a (σ a)) with hτ
  have hτs : {x | τ x ≠ x} ⊆ s := by
    intro x hx
    simp only [τ, Ne, Set.mem_setOf_eq, Equiv.swap_comp_apply] at hx
    split_ifs at hx with h₁ h₂
    · obtain rfl | hax := eq_or_ne x a
      · contradiction
      · exact mem_of_mem_insert_of_ne (hσ fun h ↦ hax <| h.symm.trans h₁) hax
    · exact (hx <| σ.injective h₂.symm).elim
    · exact mem_of_mem_insert_of_ne (hσ hx) (ne_of_apply_ne _ h₂)
  specialize hind (hfg.subset <| subset_insert _ _) hτs
  simp_rw [Finset.sum_insert has]
  grw [← hind]
  obtain hσa | hσa := eq_or_ne a (σ a)
  · rw [hτ, ← hσa, swap_self, trans_refl]
  have h1s : σ.symm a ∈ s := by
    rw [Ne, ← inv_eq_iff_eq] at hσa
    refine mem_of_mem_insert_of_ne (hσ fun h ↦ hσa ?_) hσa
    rwa [apply_symm_apply, eq_comm] at h
  simp only [← s.sum_erase_add _ h1s, add_comm]
  rw [← add_assoc, ← add_assoc]
  simp only [hτ, swap_apply_left, Function.comp_apply, Equiv.coe_trans, apply_symm_apply]
  refine add_le_add (smul_add_smul_le_smul_add_smul' ?_ ?_) (Finset.sum_congr rfl fun x hx ↦ ?_).le
  · specialize hamax (σ.symm a) h1s
    rw [Prod.Lex.toLex_le_toLex] at hamax
    rcases hamax with hamax | hamax
    · exact hfg (mem_insert_of_mem h1s) (mem_insert_self _ _) hamax
    · exact hamax.2
  · specialize hamax (σ a) (mem_of_mem_insert_of_ne (hσ <| σ.injective.ne hσa.symm) hσa.symm)
    rw [Prod.Lex.toLex_le_toLex] at hamax
    rcases hamax with hamax | hamax
    · exact hamax.le
    · exact hamax.1.le
  · rw [mem_erase, Ne, eq_symm_apply] at hx
    rw [swap_apply_of_ne_of_ne hx.1 (σ.injective.ne _)]
    rintro rfl
    exact has hx.2

