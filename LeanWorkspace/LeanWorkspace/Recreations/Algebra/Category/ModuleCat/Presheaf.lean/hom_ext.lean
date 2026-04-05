import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem hom_ext {f g : M₁ ⟶ M₂} (h : ∀ (X : Cᵒᵖ), f.app X = g.app X) :
    f = g := Hom.ext (by ext1; apply h)

