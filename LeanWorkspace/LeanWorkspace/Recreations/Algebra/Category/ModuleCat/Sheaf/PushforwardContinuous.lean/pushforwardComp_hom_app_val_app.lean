import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable {K' : GrothendieckTopology D'} {K'' : GrothendieckTopology D''}
  {G : D ⥤ D'} {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous G K K'] [Functor.IsContinuous (F ⋙ G) J K']
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')

theorem pushforwardComp_hom_app_val_app (M U x) :
  ((SheafOfModules.pushforwardComp φ ψ).hom.app M).val.app U x = x := rfl

-- Not a simp because the type of the LHS is dsimp-able

