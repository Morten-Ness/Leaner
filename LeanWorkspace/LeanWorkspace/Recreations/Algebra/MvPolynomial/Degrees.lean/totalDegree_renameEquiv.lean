import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

theorem totalDegree_renameEquiv (f : σ ≃ τ) (p : MvPolynomial σ R) :
    (renameEquiv R f p).totalDegree = p.totalDegree := (MvPolynomial.totalDegree_rename_le f p).antisymm (le_trans (by simp) (MvPolynomial.totalDegree_rename_le f.symm _))

