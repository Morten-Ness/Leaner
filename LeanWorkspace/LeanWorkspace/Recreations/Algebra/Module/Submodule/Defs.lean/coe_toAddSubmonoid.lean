import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

theorem coe_toAddSubmonoid (p : Submodule R M) : (p.toAddSubmonoid : Set M) = p := rfl

