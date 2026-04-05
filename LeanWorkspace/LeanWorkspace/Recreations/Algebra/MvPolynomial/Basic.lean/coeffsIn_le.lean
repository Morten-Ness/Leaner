import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

variable [Module R S] {M N : Submodule R S} {p : MvPolynomial σ S} {s : σ} {i : σ →₀ ℕ} {x : S}
  {n : ℕ}

theorem coeffsIn_le {N : Submodule R (MvPolynomial σ S)} :
    MvPolynomial.coeffsIn σ M ≤ N ↔ ∀ m ∈ M, ∀ i, MvPolynomial.monomial i m ∈ N := by
  simp [MvPolynomial.coeffsIn_eq_span_monomial, Submodule.span_le, Set.subset_def,
    forall_comm (α := MvPolynomial σ S)]

