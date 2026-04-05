import Mathlib

variable {R A B M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable [Semiring A] [Semiring B] [Module A M] [Module B M]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R A M] [IsScalarTower R B M]

variable [SMulCommClass A B M]

theorem smul_mem (p : Submodule (A ⊗[R] B) M) (a : A) {m : M} (hm : m ∈ p) : a • m ∈ p := by
  suffices a • m = a ⊗ₜ[R] (1 : B) • m by exact this.symm ▸ p.smul_mem _ hm
  simp [TensorProduct.Algebra.smul_def]

