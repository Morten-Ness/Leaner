import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

set_option backward.privateInPublic true in
private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p := Set.biInter_subset_of_mem


set_option backward.privateInPublic true in
private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S := Set.subset_iInter₂


theorem toAddSubmonoid_sSup (s : Set (Submodule R M)) :
    (sSup s).toAddSubmonoid = sSup (toAddSubmonoid '' s) := by
  let p : Submodule R M :=
    { toAddSubmonoid := sSup (toAddSubmonoid '' s)
      smul_mem' := fun t {m} h ↦ by
        simp_rw [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, sSup_eq_iSup'] at h ⊢
        induction h using AddSubmonoid.iSup_induction' with
        | mem p x hx =>
          obtain ⟨-, ⟨p : Submodule R M, hp : p ∈ s, rfl⟩⟩ := p
          suffices p.toAddSubmonoid ≤ ⨆ q : toAddSubmonoid '' s, (q : AddSubmonoid M) by
            exact this (smul_mem p t hx)
          apply le_sSup
          rw [Subtype.range_coe_subtype]
          exact ⟨p, hp, rfl⟩
        | zero => simpa only [smul_zero] using zero_mem _
        | add _ _ _ _ mx my => revert mx my; simp_rw [smul_add]; exact add_mem }
  refine le_antisymm (?_ : sSup s ≤ p) ?_
  · exact sSup_le fun q hq ↦ le_sSup <| Set.mem_image_of_mem toAddSubmonoid hq
  · exact sSup_le fun _ ⟨q, hq, hq'⟩ ↦ hq'.symm ▸ le_sSup hq

