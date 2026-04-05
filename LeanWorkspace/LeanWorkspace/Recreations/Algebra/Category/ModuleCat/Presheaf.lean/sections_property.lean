import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem sections_property {M : PresheafOfModules.{v} R} (s : M.sections)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) : M.map f (s.1 X) = s.1 Y := s.2 f

