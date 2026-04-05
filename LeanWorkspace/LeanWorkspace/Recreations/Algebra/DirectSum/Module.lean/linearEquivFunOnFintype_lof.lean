import Mathlib

variable {R : Type u} [Semiring R]

variable {ι : Type v}

variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

variable [DecidableEq ι]

variable {N : Type u₁} [AddCommMonoid N] [Module R N]

variable (φ : ∀ i, M i →ₗ[R] N)

variable (ψ : (⨁ i, M i) →ₗ[R] N)

variable {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}

theorem linearEquivFunOnFintype_lof [Fintype ι] (i : ι) (m : M i) :
    (DirectSum.linearEquivFunOnFintype R ι M) (DirectSum.lof R ι M i m) = Pi.single i m := by
  rfl

