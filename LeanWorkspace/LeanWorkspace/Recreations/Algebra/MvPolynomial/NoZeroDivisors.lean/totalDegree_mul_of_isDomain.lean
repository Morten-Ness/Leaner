import Mathlib

variable {R : Type*}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R]

variable {p q : MvPolynomial σ R}

variable [NoZeroDivisors R]

set_option backward.isDefEq.respectTransparency false in
theorem totalDegree_mul_of_isDomain {f g : MvPolynomial σ R}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    totalDegree (f * g) = totalDegree f + totalDegree g := by
  cases exists_wellOrder σ
  simp [← degree_degLexDegree (σ := σᵒᵈ), MonomialOrder.degree_mul hf hg]

