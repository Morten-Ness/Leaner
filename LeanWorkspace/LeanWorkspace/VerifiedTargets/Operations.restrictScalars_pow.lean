import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

variable {M : Type*} [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

variable [IsScalarTower R A A]

variable (S T : Set A) {M N P Q : Submodule R A} {m n : A}

variable {ι : Sort uι}

theorem restrictScalars_pow {A B C : Type*} [Semiring A] [Semiring B]
    [Semiring C] [SMul A B] [Module A C] [Module B C]
    [IsScalarTower A C C] [IsScalarTower B C C] [IsScalarTower A B C]
    {I : Submodule B C} :
    ∀ {n : ℕ}, (hn : n ≠ 0) → (I ^ n).restrictScalars A = I.restrictScalars A ^ n
  | 1, _ => by simp [Submodule.pow_one]
  | n + 2, _ => by
    simp [Submodule.pow_succ (n := n + 1), Submodule.restrictScalars_mul, restrictScalars_pow n.succ_ne_zero]

