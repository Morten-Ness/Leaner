import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

theorem to_singleFunctor_obj_eq_zero_of_injective {I : C} [Function.Injective I]
    {K : CochainComplex C ℤ} {i : ℤ}
    (φ : Q.obj K ⟶ Q.obj ((CochainComplex.singleFunctor C i).obj I))
    (n : ℤ) (hn : i < n) [K.IsStrictlyGE n] :
    φ = 0 := by
  obtain ⟨L, _, g, ι, h, rfl⟩ := left_fac_of_isStrictlyGE φ i
  have hπ : IsSplitMono ι := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitMono_from_singleFunctor_obj_of_injective ι
  have h₁ : inv (Q.map ι) = Q.map (retraction ι) := by
    rw [← cancel_epi (Q.map ι), IsIso.hom_inv_id, ← Q.map_comp, IsSplitMono.id, Q.map_id]
  have h₂ : g ≫ retraction ι = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    apply (K.isZero_of_isStrictlyGE n i hn).eq_of_src
  rw [h₁, ← Q.map_comp, h₂, Q.map_zero]

