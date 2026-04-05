import Mathlib

variable {R S M M₂ : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

theorem IsAddUnit.smul_right (hr : IsAddUnit r) : IsAddUnit (r • x) := hr.map (AddMonoidHom.flip (smulAddHom R M) x)

