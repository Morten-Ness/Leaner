import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem eq_C_of_isEmpty [IsEmpty σ] (p : MvPolynomial σ R) :
    p = MvPolynomial.C (p.coeff 0) := by
  obtain ⟨x, rfl⟩ := MvPolynomial.C_surjective σ p
  simp

