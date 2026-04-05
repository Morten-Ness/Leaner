import Mathlib

variable {R R₂ S M M₁ M₂ M₃ N₁ : Type*}

variable [Semiring R] [AddCommMonoid M] [AddCommGroup N₁] [Module R M] [Module R N₁]

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M]

variable {f' : End R M}

theorem iterate_succ' (n : ℕ) : f' ^ (n + 1) = .comp f' (f' ^ n) := by rw [pow_succ', Module.End.mul_eq_comp]

