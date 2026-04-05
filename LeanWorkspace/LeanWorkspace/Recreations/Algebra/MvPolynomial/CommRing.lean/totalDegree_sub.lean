import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

theorem totalDegree_sub (a b : MvPolynomial σ R) :
    (a - b).totalDegree ≤ max a.totalDegree b.totalDegree := calc
    (a - b).totalDegree = (a + -b).totalDegree := by rw [sub_eq_add_neg]
    _ ≤ max a.totalDegree (-b).totalDegree := totalDegree_add a (-b)
    _ = max a.totalDegree b.totalDegree := by rw [MvPolynomial.totalDegree_neg]

