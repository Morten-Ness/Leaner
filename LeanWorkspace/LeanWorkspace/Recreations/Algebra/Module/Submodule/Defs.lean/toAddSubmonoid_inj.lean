import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

theorem toAddSubmonoid_inj : p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q := Submodule.toAddSubmonoid_injective.eq_iff

