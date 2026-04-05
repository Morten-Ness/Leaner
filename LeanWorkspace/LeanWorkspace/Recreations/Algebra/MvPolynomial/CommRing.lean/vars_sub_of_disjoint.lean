import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

theorem vars_sub_of_disjoint [DecidableEq σ] (hpq : Disjoint p.vars q.vars) :
    (p - q).vars = p.vars ∪ q.vars := by
  rw [← MvPolynomial.vars_neg q] at hpq
  convert vars_add_of_disjoint hpq using 2 <;> simp [sub_eq_add_neg]

