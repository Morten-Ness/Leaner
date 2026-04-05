import Mathlib

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

theorem add_val {M N : SheafOfModules.{v} R} (f g : M ⟶ N) :
    (f + g).val = f.val + g.val := rfl

