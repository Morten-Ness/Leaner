import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable {ι : Sort uι}

theorem bot_pow : ∀ {n : ℕ}, n ≠ 0 → (⊥ : Submodule R A) ^ n = ⊥
  | 1, _ => Submodule.pow_one _
  | n + 2, _ => by rw [Submodule.pow_succ, bot_pow n.succ_ne_zero, Submodule.bot_mul]
