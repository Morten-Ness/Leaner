import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable {ι : Sort uι}

theorem pow_toAddSubmonoid {n : ℕ} (h : n ≠ 0) : (M ^ n).toAddSubmonoid = M.toAddSubmonoid ^ n := by
  induction n with
  | zero => exact (h rfl).elim
  | succ n ih =>
    rw [Submodule.pow_succ, Submodule.pow_succ, Submodule.mul_toAddSubmonoid]
    cases n with
    | zero => rw [Submodule.pow_zero, Submodule.pow_zero, Submodule.one_mul, ← Submodule.mul_toAddSubmonoid, Submodule.one_mul]
    | succ n => rw [ih n.succ_ne_zero]

