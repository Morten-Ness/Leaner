import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (M M₁ M₂ : PresheafOfModules.{v} R)

theorem sectionsMap_id {M : PresheafOfModules.{v} R} (s : M.sections) :
    PresheafOfModules.sectionsMap (𝟙 M) s = s := rfl

