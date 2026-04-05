import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

theorem sectionsMap_comp {M N P : SheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections) :
    sectionsMap (f ≫ g) s = sectionsMap g (sectionsMap f s) := rfl

