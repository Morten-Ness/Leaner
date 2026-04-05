import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

variable [HasDerivedCategory.{w} C]

theorem from_singleFunctor_obj_eq_zero_of_projective {P : C} [Projective P]
    {L : CochainComplex C ℤ} {i : ℤ}
    (φ : Q.obj ((CochainComplex.singleFunctor C i).obj P) ⟶ Q.obj L)
    (n : ℤ) (hn : n < i) [L.IsStrictlyLE n] :
    φ = 0 := by
  obtain ⟨K, _, π, h, g, rfl⟩ := right_fac_of_isStrictlyLE φ i
  have hπ : IsSplitEpi π := by
    rw [isIso_Q_map_iff_quasiIso] at h
    exact CochainComplex.isSplitEpi_to_singleFunctor_obj_of_projective π
  have h₁ : inv (Q.map π) = Q.map (section_ π) := by
    rw [← cancel_mono (Q.map π), IsIso.inv_hom_id, ← Q.map_comp, IsSplitEpi.id, Q.map_id]
  have h₂ : section_ π ≫ g = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    apply (L.isZero_of_isStrictlyLE n i hn).eq_of_tgt
  rw [h₁, ← Q.map_comp, h₂, Q.map_zero]

