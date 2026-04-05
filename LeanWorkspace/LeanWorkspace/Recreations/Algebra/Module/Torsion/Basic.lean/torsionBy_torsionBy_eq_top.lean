import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBy_torsionBy_eq_top : Submodule.torsionBy R (Submodule.torsionBy R M a) a = ⊤ := (Module.isTorsionBy_iff_torsionBy_eq_top a).mp <| Submodule.torsionBy_isTorsionBy a

