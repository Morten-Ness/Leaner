import Mathlib

open scoped Pointwise

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] [CommSemiring S₁] {p q : MvPolynomial σ R}

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

variable [Module R S] {M N : Submodule R S} {p : MvPolynomial σ S} {s : σ} {i : σ →₀ ℕ} {x : S}
  {n : ℕ}

theorem coeffsIn_eq_span_monomial : MvPolynomial.coeffsIn σ M = .span R {MvPolynomial.monomial i m | (m ∈ M) (i : σ →₀ ℕ)} := by
  classical
  refine le_antisymm ?_ <| Submodule.span_le.2 ?_
  · rintro p hp
    rw [MvPolynomial.as_sum p]
    exact sum_mem fun i hi ↦ Submodule.subset_span ⟨_, hp i, _, rfl⟩
  · rintro _ ⟨m, hm, s, n, rfl⟩ i
    simp
    split <;> simp [hm]

