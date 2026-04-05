import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_torsionBySet_eq_top : Submodule.torsionBySet R (Submodule.torsionBySet R M s) s = ⊤ := (Module.isTorsionBySet_iff_torsionBySet_eq_top s).mp <| Submodule.torsionBySet_isTorsionBySet s

