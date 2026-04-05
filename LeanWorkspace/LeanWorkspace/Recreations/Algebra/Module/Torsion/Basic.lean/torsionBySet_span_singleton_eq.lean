import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBySet_span_singleton_eq : Submodule.torsionBySet R M (R ∙ a) = Submodule.torsionBy R M a := (Submodule.torsionBySet_eq_torsionBySet_span _).symm.trans <| Submodule.torsionBySet_singleton_eq _

