import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

theorem degree_optionEquivLeft {f : MvPolynomial (Option σ) R} (h : f ≠ 0) :
    (MvPolynomial.optionEquivLeft R σ f).degree = degreeOf none f := by
  have h' : ((MvPolynomial.optionEquivLeft R σ f).support.sup fun x => x) = degreeOf none f := by
    rw [degreeOf_eq_sup, MvPolynomial.support_optionEquivLeft, Finset.sup_image, Function.comp_def]
  rw [Polynomial.degree, ← h', Nat.cast_withBot,
    Finset.coe_sup_of_nonempty (MvPolynomial.nonempty_support_optionEquivLeft R h), Finset.max_eq_sup_coe,
    Function.comp_def]

