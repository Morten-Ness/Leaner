import Mathlib

variable {R : Type u} {S : Type v}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommRing R]

variable {p q : MvPolynomial σ R}

theorem vars_sub_subset [DecidableEq σ] : (p - q).vars ⊆ p.vars ∪ q.vars := by
  convert vars_add_subset p (-q) using 2 <;> simp [sub_eq_add_neg]

