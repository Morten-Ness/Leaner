import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (eqv : C ≌ D)
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous eqv.functor J K]
  [Functor.IsContinuous eqv.inverse K J]
  (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj)

theorem pushforwardPushforwardEquivalence_counit_app_val_app (M U x) :
    ((pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).counit.app M).val.app U x =
      M.val.map (eqv.unit.app U.unop).op x := rfl

