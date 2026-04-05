import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem optionEquivLeft_coeff_some_coeff_none
    (n : Option S₁ →₀ ℕ) (f : MvPolynomial (Option S₁) R) :
    coeff n.some (Polynomial.coeff (MvPolynomial.optionEquivLeft R S₁ f) (n none)) = coeff n f := by
  induction f using MvPolynomial.induction_on' generalizing n with
  | monomial j r =>
    rw [MvPolynomial.optionEquivLeft_monomial]
    classical
    simp only [Polynomial.coeff_monomial, MvPolynomial.coeff_monomial, apply_ite]
    simp only [coeff_zero]
    by_cases hj : j = n
    · simp [hj]
    · rw [if_neg hj]
      simp only [ite_eq_right_iff]
      intro hj_none hj_some
      apply False.elim (hj _)
      simp only [Finsupp.ext_iff, Option.forall, hj_none, true_and]
      simpa only [Finsupp.ext_iff] using hj_some
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]

