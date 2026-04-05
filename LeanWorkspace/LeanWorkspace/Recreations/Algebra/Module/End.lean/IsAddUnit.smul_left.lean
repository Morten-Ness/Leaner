import Mathlib

variable {R S M M₂ : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

theorem IsAddUnit.smul_left [DistribSMul S M] (hx : IsAddUnit x) (s : S) :
    IsAddUnit (s • x) := hx.map (DistribSMul.toAddMonoidHom M s)

