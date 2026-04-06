FAIL
import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable {ι : Sort _}

theorem pow_mem_pow {x : A} (hx : x ∈ M) (n : ℕ) : x ^ n ∈ M ^ n := by
  induction n with
  | zero =>
      simpa [pow_zero] using (show (1 : A) ∈ (1 : Submodule R A) from Submodule.one_mul_mem_one)
  | succ n ih =>
      rw [pow_succ, Submodule.pow_succ]
      exact Submodule.mul_mem_mul hx ih
