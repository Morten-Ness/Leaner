import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

theorem pow_apply (f : Module.End R M) (n : ℕ) (m : M) : (f ^ n) m = f^[n] m := congr_fun (Module.End.coe_pow f n) m

