import Mathlib

variable {R : Type*}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

variable [NoZeroDivisors R]

theorem degrees_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) :
    degrees (p * q) = degrees p + degrees q := by
  classical
  ext s
  simp_rw [Multiset.count_add, ← degreeOf_def, MvPolynomial.degreeOf_mul_eq hp hq]

