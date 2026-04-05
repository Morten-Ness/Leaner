import Mathlib

section

variable {C : Type*} [SmallCategory C] [IsFiltered C] (R : C ⥤ RingCat) (M : C ⥤ Ab)
    [∀ i, Module (R.obj i) (M.obj i)]
    (H : ∀ {i j} (f : i ⟶ j) r m, M.map f (r • m) = R.map f r • M.map f m)

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in
set_option backward.isDefEq.respectTransparency false in
theorem IsColimit.ι_smul {cR : Cocone R} (hcR : IsColimit cR) {cM : Cocone M}
    (hcM : IsColimit cM) (i : C) (r : R.obj i) (m : M.obj i) :
    letI := IsColimit.module R M H hcR hcM
    cM.ι.app i (r • m) =
      HSMul.hSMul (α := cR.pt) (β := cM.pt) (cR.ι.app i r) (cM.ι.app i m) := by
  letI := filteredColimitsModule R M H
  let α := IsColimit.coconePointUniqueUpToIso hcM
    (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit M)
  let β := IsColimit.coconePointUniqueUpToIso hcR
    (RingCat.FilteredColimits.colimitCoconeIsColimit R)
  apply α.addCommGroupIsoToAddEquiv.eq_symm_apply.mpr ?_
  change (cM.ι.app i ≫ α.hom) _ = (HSMul.hSMul (α := RingCat.FilteredColimits.colimit R)
    (β := AddCommGrpCat.FilteredColimits.colimit M)
    ((cR.ι.app i ≫ β.hom) r) ((cM.ι.app i ≫ α.hom) m))
  simp only [Functor.const_obj_obj, comp_coconePointUniqueUpToIso_hom, α, β]
  obtain ⟨s, α, H⟩ := IsFilteredOrEmpty.cocone_maps (leftToMax i i) (rightToMax i i)
  refine Functor.ιColimitType_eq_of_map_eq_map _ _ _ (leftToMax _ _ ≫ α) α ?_
  dsimp
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, *]

end

section

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{u}} (M : PresheafOfModules.{u} R)

variable (x : X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem germ_ringCat_smul (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    TopCat.Presheaf.germ M.presheaf U x hx (r • m) =
      R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m := letI (i : (OpenNhds x)ᵒᵖ) : Module (((OpenNhds.inclusion x).op ⋙ R).obj i)
      (((OpenNhds.inclusion x).op ⋙ M.presheaf).obj i) := by
    dsimp; infer_instance
  Limits.IsColimit.ι_smul ((OpenNhds.inclusion x).op ⋙ R) ((OpenNhds.inclusion x).op ⋙ M.presheaf)
    (fun f r m ↦ M.map_smul _ _ _)
      (Limits.colimit.isColimit _) (Limits.colimit.isColimit _) ⟨_, _⟩ _ _

end

section

variable {X : TopCat.{u}} {R : X.Presheaf RingCat.{u}} (M : PresheafOfModules.{u} R)

variable (x : X)

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem germ_smul (x : X) (U : Opens X) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    TopCat.Presheaf.germ M.presheaf U x hx (r • m) =
      R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m := letI (i : (OpenNhds x)ᵒᵖ) : Module (((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ _ RingCat).obj i)
      (((OpenNhds.inclusion x).op ⋙ M.presheaf).obj i) := by
    dsimp; infer_instance
  Limits.IsColimit.ι_smul ((OpenNhds.inclusion x).op ⋙ R ⋙ forget₂ _ _)
    ((OpenNhds.inclusion x).op ⋙ M.presheaf)
    (fun f r m ↦ M.map_smul _ _ _) (Limits.isColimitOfPreserves (forget₂ _ _)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙ R))) (Limits.colimit.isColimit _)
      ⟨_, _⟩ _ _

end
