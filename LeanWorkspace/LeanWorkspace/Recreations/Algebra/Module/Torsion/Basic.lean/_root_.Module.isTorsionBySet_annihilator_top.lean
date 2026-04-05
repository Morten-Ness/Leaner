import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

theorem _root_.Module.isTorsionBySet_annihilator_top :
    Module.IsTorsionBySet R M (⊤ : Submodule R M).annihilator := fun x ha =>
  mem_annihilator.mp ha.prop x mem_top

