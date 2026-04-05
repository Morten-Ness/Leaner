import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable [Algebra R S₁] [CommSemiring S₂]

variable (f : σ → S₁)

theorem _root_.Algebra.adjoin_range_eq_range_aeval :
    Algebra.adjoin R (Set.range f) = (MvPolynomial.aeval f).range := by
  simp only [← Algebra.map_top, ← MvPolynomial.adjoin_range_X, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, MvPolynomial.aeval_X]

