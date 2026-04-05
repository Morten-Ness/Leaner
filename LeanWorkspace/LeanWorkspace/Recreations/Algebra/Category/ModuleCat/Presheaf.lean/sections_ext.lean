import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem sections_ext {M : PresheafOfModules.{v} R} (s t : M.sections)
    (h : ∀ (X : Cᵒᵖ), s.val X = t.val X) : s = t := Subtype.ext (by ext; apply h)

