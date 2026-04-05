import Mathlib

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

theorem pullbackObjIsDefined_eq_top :
    pullbackObjIsDefined.{u} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _)
  all_goals
    apply leftAdjointObjIsDefined_colimit _
      (fun _ ↦ PresheafOfModules.pullbackObjIsDefined_free_yoneda _ _)

