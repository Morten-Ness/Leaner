import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

theorem sectionsMap_id {M : SheafOfModules.{v} R} (s : M.sections) :
    sectionsMap (𝟙 M) s = s := rfl

