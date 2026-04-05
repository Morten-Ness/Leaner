import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {p q : Submodule R M}

theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

