import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {S' R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))
  (φ : S ⟶ F.op ⋙ R) (φ' : S' ⟶ R)

theorem congr_d {d d' : M.Derivation φ} (h : d = d') {X : Dᵒᵖ} (b : R.obj X) :
    d.d b = d'.d b := by rw [h]

