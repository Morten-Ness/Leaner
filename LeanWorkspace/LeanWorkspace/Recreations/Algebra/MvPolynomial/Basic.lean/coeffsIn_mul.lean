import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

variable [Algebra R S] {M : Submodule R S}

theorem coeffsIn_mul (M N : Submodule R S) : MvPolynomial.coeffsIn σ (M * N) = MvPolynomial.coeffsIn σ M * MvPolynomial.coeffsIn σ N := by
  classical
  refine le_antisymm (MvPolynomial.coeffsIn_le.2 ?_) ?_
  · intro r hr s
    induction hr using Submodule.mul_induction_on' with
    | mem_mul_mem m hm n hn =>
      rw [← add_zero s, ← MvPolynomial.monomial_mul]
      apply Submodule.mul_mem_mul <;> simpa
    | add x _ y _ hx hy =>
      simpa [map_add] using add_mem hx hy
  · rw [Submodule.mul_le]
    intro x hx y hy k
    rw [MvPolynomial.coeff_mul]
    exact sum_mem fun c hc ↦ Submodule.mul_mem_mul (hx _) (hy _)

