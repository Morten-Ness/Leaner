import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable [Algebra R S₁] [CommSemiring S₂]

variable (f : σ → S₁)

theorem comp_aeval_apply {B : Type*} [CommSemiring B] [Algebra R B] (φ : S₁ →ₐ[R] B)
    (p : MvPolynomial σ R) :
    φ (MvPolynomial.aeval f p) = MvPolynomial.aeval (fun i ↦ φ (f i)) p := by
  rw [← MvPolynomial.comp_aeval, AlgHom.coe_comp, comp_apply]

