import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

theorem toSubMulAction_mono : Monotone (toSubMulAction : Submodule R M → SubMulAction R M) := Submodule.toSubMulAction_strictMono.monotone

