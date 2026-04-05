import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

set_option backward.isDefEq.respectTransparency false in
theorem pushforwardSections_unitHomEquiv
    {M : SheafOfModules.{u} R} (f : unit R ⟶ M) :
    SheafOfModules.pushforwardSections φ (M.unitHomEquiv f) =
      ((pushforward φ).obj M).unitHomEquiv
        (SheafOfModules.unitToPushforwardObjUnit φ ≫ (pushforward φ).map f) := by
  ext X
  have := SheafOfModules.unitToPushforwardObjUnit_val_app_apply φ (X := X) 1
  dsimp at this ⊢
  simp +instances [this, map_one]
  rfl

