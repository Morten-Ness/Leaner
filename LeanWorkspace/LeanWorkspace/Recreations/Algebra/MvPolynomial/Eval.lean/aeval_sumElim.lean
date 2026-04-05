import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {S T : Type*} [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T] [Algebra S T]
  [IsScalarTower R S T]

theorem aeval_sumElim {σ τ : Type*} (p : MvPolynomial (σ ⊕ τ) R) (f : τ → S) (g : σ → T) :
    (MvPolynomial.aeval (Sum.elim g (algebraMap S T ∘ f))) p =
      (MvPolynomial.aeval g) ((MvPolynomial.aeval (Sum.elim X (C ∘ f))) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [← IsScalarTower.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i h => cases i <;> simp [h]

