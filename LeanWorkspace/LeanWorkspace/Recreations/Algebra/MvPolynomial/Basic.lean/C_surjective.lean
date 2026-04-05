import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem C_surjective {R : Type*} [CommSemiring R] (σ : Type*) [IsEmpty σ] :
    Function.Surjective (MvPolynomial.C : R → MvPolynomial σ R) := by
  refine fun p => ⟨p.toFun 0, Finsupp.ext fun a => ?_⟩
  simp only [MvPolynomial.C_apply, ← MvPolynomial.single_eq_monomial, (Finsupp.ext isEmptyElim (α := σ) : a = 0),
    single_eq_same]
  rfl

