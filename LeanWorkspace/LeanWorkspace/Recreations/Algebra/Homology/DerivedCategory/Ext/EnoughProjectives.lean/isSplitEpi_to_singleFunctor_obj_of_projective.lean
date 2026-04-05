import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem isSplitEpi_to_singleFunctor_obj_of_projective
    {P : C} [Projective P] {K : CochainComplex C ℤ} {i : ℤ}
    (π : K ⟶ (CochainComplex.singleFunctor C i).obj P) [K.IsStrictlyLE i] [QuasiIsoAt π i] :
    IsSplitEpi π := by
  let e := K.iCyclesIso i (i + 1) (by simp)
    ((K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt _ _)
  let α := e.inv ≫ K.homologyπ i ≫ homologyMap π i ≫ (singleObjHomologySelfIso _ _ _).hom
  have : π.f i = α ≫ (singleObjXSelf (ComplexShape.up ℤ) i P).inv := by
    rw [← cancel_epi e.hom]
    dsimp [α, e]
    rw [assoc, assoc, assoc, iCyclesIso_hom_inv_id_assoc,
      homologyπ_naturality_assoc]
    dsimp [singleFunctor, singleFunctors]
    rw [homologyπ_singleObjHomologySelfIso_hom_assoc,
      ← singleObjCyclesSelfIso_inv_iCycles, Iso.hom_inv_id_assoc, ← cyclesMap_i]
  exact ⟨⟨{
    section_ := mkHomFromSingle (Projective.factorThru (𝟙 P) α) (by
      rintro _ rfl
      apply (K.isZero_of_isStrictlyLE i (i + 1) (by simp)).eq_of_tgt)
    id := by
      apply HomologicalComplex.from_single_hom_ext
      rw [comp_f, mkHomFromSingle_f, assoc, id_f, this, Projective.factorThru_comp_assoc,
        id_comp, Iso.hom_inv_id]
      rfl }⟩⟩

