import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {S' R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))
  (φ : S ⟶ F.op ⋙ R) (φ' : S' ⟶ R)

variable (d : ∀ (X : Dᵒᵖ), (M.obj X).Derivation (φ'.app X))

variable (d_map : ∀ ⦃X Y : Dᵒᵖ⦄ (f : X ⟶ Y) (x : R.obj X),
      (d Y).d ((R.map f) x) = (M.map f) ((d X).d x))

theorem mk_app (X : Dᵒᵖ) : (PresheafOfModules.Derivation'.mk d d_map).app X = d X := rfl

