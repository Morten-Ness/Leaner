import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

theorem toSubMulAction_inj : p.toSubMulAction = q.toSubMulAction ↔ p = q := Submodule.toSubMulAction_injective.eq_iff

