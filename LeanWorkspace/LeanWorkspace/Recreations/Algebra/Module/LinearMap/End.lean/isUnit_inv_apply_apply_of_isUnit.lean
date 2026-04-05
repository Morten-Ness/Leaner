import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

theorem isUnit_inv_apply_apply_of_isUnit {f : Module.End R M} (h : IsUnit f) (x : M) :
    h.unit.inv (f x) = x := (by simp : (h.unit.inv * f) x = x)

