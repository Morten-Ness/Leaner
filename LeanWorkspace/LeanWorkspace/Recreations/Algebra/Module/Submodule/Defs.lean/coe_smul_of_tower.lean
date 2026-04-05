import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

theorem coe_smul_of_tower [SMul S R] [SMul S M] [IsScalarTower S R M] (r : S) (x : p) :
    ((r • x : p) : M) = r • (x : M) := rfl

