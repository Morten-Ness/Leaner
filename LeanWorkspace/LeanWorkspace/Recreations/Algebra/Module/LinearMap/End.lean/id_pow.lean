import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

theorem id_pow (n : ℕ) : (id : Module.End R M) ^ n = .id := one_pow n

