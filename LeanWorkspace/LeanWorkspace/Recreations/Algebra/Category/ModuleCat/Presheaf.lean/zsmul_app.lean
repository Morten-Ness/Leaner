import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem zsmul_app (n : ℤ) (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (n • f).app X = n • f.app X := by
  ext x
  change (PresheafOfModules.toPresheaf R ⋙ (evaluation _ _).obj X).map (n • f) x = _
  rw [Functor.map_zsmul]
  rfl

