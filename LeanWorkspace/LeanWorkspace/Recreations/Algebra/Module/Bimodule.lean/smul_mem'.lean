import Mathlib

variable {R A B M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable [Semiring A] [Semiring B] [Module A M] [Module B M]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R A M] [IsScalarTower R B M]

variable [SMulCommClass A B M]

theorem smul_mem' (p : Submodule (A ⊗[R] B) M) (b : B) {m : M} (hm : m ∈ p) : b • m ∈ p := by
  suffices b • m = (1 : A) ⊗ₜ[R] b • m by exact this.symm ▸ Subbimodule.smul_mem p _ hm
  simp [TensorProduct.Algebra.smul_def]

