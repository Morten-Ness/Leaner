import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

theorem pushforward_id_comp :
    SheafOfModules.pushforwardComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerRight (SheafOfModules.pushforwardId R) (SheafOfModules.pushforward.{v} φ) ≪≫ leftUnitor _ := by ext; rfl

