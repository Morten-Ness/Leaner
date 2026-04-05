import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

theorem isUnit_apply_inv_apply_of_isUnit {f : Module.End R M} (h : IsUnit f) (x : M) :
    f (h.unit.inv x) = x := show (f * h.unit.inv) x = x by simp

