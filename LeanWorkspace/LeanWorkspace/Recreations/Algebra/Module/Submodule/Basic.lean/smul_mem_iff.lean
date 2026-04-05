import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [DivisionSemiring S] [Semiring R] [AddCommMonoid M] [Module R M]

variable [SMul S R] [Module S M] [IsScalarTower S R M]

variable (p : Submodule R M) {s : S} {x y : M}

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p := p.toSubMulAction.smul_mem_iff s0

