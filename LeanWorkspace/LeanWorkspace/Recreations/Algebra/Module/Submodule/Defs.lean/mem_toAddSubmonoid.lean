import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M] [Module R M]

theorem mem_toAddSubmonoid (p : Submodule R M) (x : M) : x ∈ p.toAddSubmonoid ↔ x ∈ p := Iff.rfl

