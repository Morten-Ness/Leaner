import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable {s t : Multiset σ}

theorem degreesLE_nsmul : ∀ n, MvPolynomial.degreesLE R σ (n • s) = MvPolynomial.degreesLE R σ s ^ n
  | 0 => by simp
  | k + 1 => by simp only [pow_succ, degreesLE_nsmul, MvPolynomial.degreesLE_add, add_smul, one_smul]
