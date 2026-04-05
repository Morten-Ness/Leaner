import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F G H : C ⥤ D} {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  [Functor.IsContinuous G J K]
  [Functor.IsContinuous H J K]
  (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S)

theorem pushforwardNatTrans_app_val_app_apply (α : F ⟶ G) (X U x) :
    ((SheafOfModules.pushforwardNatTrans φ α).app X).val.app U x = X.val.map (α.app U.unop).op x := rfl

