import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

theorem toAddSubmonoid_injective : Function.Injective (toAddSubmonoid : Submodule R M → AddSubmonoid M) := fun p q h => SetLike.ext'_iff.2 (show (p.toAddSubmonoid : Set M) = q from SetLike.ext'_iff.1 h)

