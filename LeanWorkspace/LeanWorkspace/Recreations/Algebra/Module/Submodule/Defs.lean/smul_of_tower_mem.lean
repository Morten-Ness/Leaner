import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

theorem smul_of_tower_mem [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (h : x ∈ p) :
    r • x ∈ p := p.toSubMulAction.smul_of_tower_mem r h

