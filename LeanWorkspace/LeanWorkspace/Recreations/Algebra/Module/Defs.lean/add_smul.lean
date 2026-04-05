import Mathlib

variable {R S M M₂ : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

theorem add_smul : (r + s) • x = r • x + s • x := Module.add_smul r s x

