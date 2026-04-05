import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

theorem conjugateEquiv_pullbackId_hom :
    conjugateEquiv .id (SheafOfModules.pullbackPushforwardAdjunction.{v} _) (SheafOfModules.pullbackId S).hom =
      (pushforwardId S).inv := Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _

