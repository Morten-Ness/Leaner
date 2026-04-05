import Mathlib

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

theorem restr_inf_cartan_eq_biSup_corootSubmodule (I : LieIdeal K L) :
    I.restr H ⊓ H.toLieSubmodule = ⨆ α ∈ I.rootSet, corootSubmodule α.1 := by
  refine le_antisymm ?_ (iSup₂_le fun _ hα ↦
    le_inf (I.corootSubmodule_le hα) LieSubmodule.map_incl_le)
  intro x ⟨hxI, hxH⟩
  let f : H.root → LieIdeal K H := fun α ↦ corootSpace α.1
  set span_I_roots := ⨆ α ∈ I.rootSet, f α
  set span_compl_roots := ⨆ (β : H.root) (_ : β ∉ I.rootSet), f β
  have h_split : span_I_roots ⊔ span_compl_roots = ⨆ α, f α :=
    (iSup_split f (· ∈ I.rootSet)).symm
  have h_top : span_I_roots ⊔ span_compl_roots = ⊤ := by
    rw [h_split, eq_top_iff, ← biSup_corootSpace_eq_top]
    exact iSup₂_le fun α hα ↦ le_iSup_of_le ⟨α, by simpa [LieSubalgebra.root] using hα⟩ le_rfl
  have hspan_I_roots_incl : LieSubmodule.map H.toLieSubmodule.incl span_I_roots =
      ⨆ α ∈ I.rootSet, corootSubmodule α.1 := by
    change LieSubmodule.map _ (⨆ α ∈ I.rootSet, f α) = ⨆ α ∈ I.rootSet, _
    simp_rw [LieSubmodule.map_iSup]; rfl
  have hspan_compl_roots_vanish (μ : H.root) (hμ : μ ∈ I.rootSet) :
      span_compl_roots.toSubmodule ≤ μ.1.ker := by
    have : span_compl_roots.toSubmodule = ⨆ β ∉ I.rootSet, (f β).toSubmodule := by
      simp_rw [span_compl_roots, LieSubmodule.iSup_toSubmodule]
    rw [this]
    exact iSup₂_le fun γ hγ ↦ by
      rw [coe_corootSpace_eq_span_singleton, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hμ hγ
  have hx_top : (⟨x, hxH⟩ : H) ∈ span_I_roots ⊔ span_compl_roots := h_top ▸ trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx_top
  have haI : (a : L) ∈ I :=
    (iSup₂_le (fun _ hα ↦ I.corootSubmodule_le hα) :
      ⨆ α ∈ I.rootSet, corootSubmodule α.1 ≤ _)
      (hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha)
  have hbI : (b : L) ∈ I := by
    have h_sum : (a : L) + b = x := congr_arg Subtype.val hab
    have h_b_eq : (b : L) = x - a := by rw [← h_sum, add_sub_cancel_left]
    rw [h_b_eq]; exact I.toSubmodule.sub_mem hxI haI
  suffices b = 0 by
    subst this; simp only [add_zero] at hab; subst hab
    exact hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha
  suffices b ∈ ⨅ α : Weight K H L, α.ker by simpa [iInf_ker_weight_eq_bot] using this
  refine (Submodule.mem_iInf _).mpr fun μ ↦ ?_
  by_cases hμ : μ.IsNonZero
  · have hμ_root : μ ∈ H.root := by simpa [LieSubalgebra.root] using hμ
    by_cases hμI : (⟨μ, hμ_root⟩ : H.root) ∈ I.rootSet
    · exact hspan_compl_roots_vanish ⟨μ, hμ_root⟩ hμI hb
    · exact I.root_apply_eq_zero_of_notMem_rootSet hbI hμI
  · simp only [Weight.IsNonZero, not_not] at hμ
    exact LinearMap.mem_ker.mpr (congr_fun hμ b)

