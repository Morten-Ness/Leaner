import Mathlib

variable {R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBySet_span_singleton_iff : IsTorsionBySet R M (R ∙ a) ↔ IsTorsionBy R M a := (Module.isTorsionBySet_iff_is_torsion_by_span _).symm.trans <| Module.isTorsionBySet_singleton_iff _

