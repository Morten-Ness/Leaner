import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

theorem smul_mem_iff' [Group G] [MulAction G M] [SMul G R] [IsScalarTower G R M] (g : G) :
    g • x ∈ p ↔ x ∈ p := p.toSubMulAction.smul_mem_iff' g

