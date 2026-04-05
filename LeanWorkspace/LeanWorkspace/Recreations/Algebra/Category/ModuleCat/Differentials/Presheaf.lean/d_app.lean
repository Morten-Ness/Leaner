import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {S' R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))
  (φ : S ⟶ F.op ⋙ R) (φ' : S' ⟶ R)

theorem d_app (d : M.Derivation' φ') {X : Dᵒᵖ} (a : S'.obj X) :
    d.d (φ'.app X a) = 0 := Derivation.d_app d _

