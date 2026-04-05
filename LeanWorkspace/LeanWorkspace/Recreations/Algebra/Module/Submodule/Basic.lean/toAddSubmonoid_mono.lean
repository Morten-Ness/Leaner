import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

theorem toAddSubmonoid_mono : Monotone (toAddSubmonoid : Submodule R M → AddSubmonoid M) := Submodule.toAddSubmonoid_strictMono.monotone

