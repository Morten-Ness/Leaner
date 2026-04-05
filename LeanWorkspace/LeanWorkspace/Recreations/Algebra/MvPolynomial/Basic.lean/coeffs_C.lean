import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem coeffs_C [DecidableEq R] (r : R) : (MvPolynomial.C (σ := σ) r).coeffs = if r = 0 then ∅ else {r} := by
  classical
  aesop (add simp MvPolynomial.mem_coeffs_iff)

