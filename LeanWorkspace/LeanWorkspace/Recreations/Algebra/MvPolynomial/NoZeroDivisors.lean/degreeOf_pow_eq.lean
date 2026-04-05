import Mathlib

variable {R : Type*}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

variable [NoZeroDivisors R]

theorem degreeOf_pow_eq (i : σ) (p : MvPolynomial σ R) (n : ℕ) (hp : p ≠ 0) :
    degreeOf i (p ^ n) = n * degreeOf i p := by
  rw [pow_eq_prod_const, MvPolynomial.degreeOf_prod_eq (range n) (fun _ ↦ p) (fun _ _ ↦ hp)]
  simp

