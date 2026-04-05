import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem degrees_monomial (s : σ →₀ ℕ) (a : R) : MvPolynomial.degrees (monomial s a) ≤ toMultiset s := by
  classical
    refine (supDegree_single s a).trans_le ?_
    split_ifs
    exacts [bot_le, le_rfl]

