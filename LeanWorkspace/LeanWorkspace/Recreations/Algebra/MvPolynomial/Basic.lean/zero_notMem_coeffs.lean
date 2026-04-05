import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

theorem zero_notMem_coeffs (p : MvPolynomial σ R) : 0 ∉ p.coeffs := by
  intro hz
  obtain ⟨n, hnsupp, hn⟩ := MvPolynomial.mem_coeffs_iff.mp hz
  exact (MvPolynomial.mem_support_iff.mp hnsupp) hn.symm

