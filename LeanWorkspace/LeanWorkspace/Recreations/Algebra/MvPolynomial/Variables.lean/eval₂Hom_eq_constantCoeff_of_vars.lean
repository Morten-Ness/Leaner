import Mathlib

variable {R : Type u} {S : Type v}

variable {σ τ : Type*} {r : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}

variable [CommSemiring R] {p q : MvPolynomial σ R}

variable [CommSemiring S]

theorem eval₂Hom_eq_constantCoeff_of_vars (f : R →+* S) {g : σ → S} {p : MvPolynomial σ R}
    (hp : ∀ i ∈ p.vars, g i = 0) : eval₂Hom f g p = f (constantCoeff p) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, eval₂Hom_monomial]
  by_cases h0 : constantCoeff p = 0
  on_goal 1 =>
    rw [h0, f.map_zero, Finset.sum_eq_zero]
    intro d hd
  on_goal 2 =>
    rw [Finset.sum_eq_single (0 : σ →₀ ℕ)]
    · rw [Finsupp.prod_zero_index, mul_one]
      rfl
    on_goal 1 => intro d hd hd0
  on_goal 3 =>
    rw [constantCoeff_eq, coeff, ← Ne, ← Finsupp.mem_support_iff] at h0
    intro
    contradiction
  repeat'
    obtain ⟨i, hi⟩ : Finset.Nonempty (Finsupp.support d) := by
      rw [constantCoeff_eq, coeff, ← Finsupp.notMem_support_iff] at h0
      rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty]
      rintro rfl
      contradiction
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    rw [hp, zero_pow (Finsupp.mem_support_iff.1 hi)]
    rw [MvPolynomial.mem_vars]
    exact ⟨d, hd, hi⟩

