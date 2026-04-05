import Mathlib

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
theorem isSplitMono_from_singleFunctor_obj_of_injective
    {I : C} [Function.Injective I] {L : CochainComplex C ℤ} {i : ℤ}
    (ι : (CochainComplex.singleFunctor C i).obj I ⟶ L) [L.IsStrictlyGE i] [QuasiIsoAt ι i] :
    IsSplitMono ι := by
  let e := L.pOpcyclesIso (i - 1) i (by simp)
    ((L.isZero_of_isStrictlyGE i (i - 1) (by simp)).eq_of_src _ _)
  let α := (singleObjHomologySelfIso _ _ _).inv ≫ homologyMap ι i ≫ L.homologyι i ≫ e.inv
  have : ι.f i = (singleObjXSelf (ComplexShape.up ℤ) i I).hom ≫ α := by
    rw [← cancel_mono e.hom]
    dsimp [α, e]
    rw [assoc, assoc, assoc, assoc, pOpcyclesIso_inv_hom_id, comp_id, homologyι_naturality]
    dsimp [singleFunctor, singleFunctors]
    rw [singleObjHomologySelfIso_inv_homologyι_assoc,
      ← pOpcycles_singleObjOpcyclesSelfIso_inv_assoc, Iso.inv_hom_id_assoc, p_opcyclesMap]
  exact ⟨⟨{
    retraction := mkHomToSingle (Function.Injective.factorThru (𝟙 I) α) (by
      rintro j rfl
      apply (L.isZero_of_isStrictlyGE (j + 1) j (by simp)).eq_of_src)
    id := by
      apply HomologicalComplex.to_single_hom_ext
      rw [comp_f, mkHomToSingle_f, id_f, this, assoc, Function.Injective.comp_factorThru_assoc,
        id_comp, Iso.hom_inv_id] }⟩⟩

