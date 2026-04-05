import Mathlib

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

variable {σ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {s : σ →₀ ℕ}

variable (R) [CommSemiring R]

variable (n : ℕ)

theorem finSuccEquiv_coeff_coeff (m : Fin n →₀ ℕ) (f : MvPolynomial (Fin (n + 1)) R) (i : ℕ) :
    coeff m (Polynomial.coeff (MvPolynomial.finSuccEquiv R n f) i) = coeff (m.cons i) f := by
  induction f using MvPolynomial.induction_on' generalizing i m with
  | add p q hp hq => simp only [map_add, Polynomial.coeff_add, coeff_add, hp, hq]
  | monomial j r =>
    simp only [MvPolynomial.finSuccEquiv_apply, coe_eval₂Hom, eval₂_monomial, RingHom.coe_comp, Finsupp.prod_pow,
      Polynomial.coeff_C_mul, coeff_C_mul, coeff_monomial, Fin.prod_univ_succ, Fin.cases_zero,
      Fin.cases_succ, ← map_prod, ← map_pow, Function.comp_apply]
    rw [← mul_boole, mul_comm (Polynomial.X ^ j 0), Polynomial.coeff_C_mul_X_pow]; congr 1
    obtain rfl | hjmi := eq_or_ne j (m.cons i)
    · simpa only [cons_zero, cons_succ, if_pos rfl, monomial_eq, C_1, one_mul,
        Finsupp.prod_pow] using coeff_monomial m m (1 : R)
    · simp only [hjmi, if_false]
      obtain hij | rfl := ne_or_eq i (j 0)
      · simp only [hij, if_false, coeff_zero]
      simp only [if_true]
      have hmj : m ≠ j.tail := by
        rintro rfl
        rw [cons_tail] at hjmi
        contradiction
      simpa only [monomial_eq, C_1, one_mul, Finsupp.prod_pow, tail_apply, if_neg hmj.symm] using
        coeff_monomial m j.tail (1 : R)

