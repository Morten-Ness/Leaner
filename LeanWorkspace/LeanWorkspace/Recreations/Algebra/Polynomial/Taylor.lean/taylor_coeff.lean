import Mathlib

variable {R : Type*} [Semiring R] (r : R) (f : R[X])

theorem taylor_coeff (n : ℕ) : (Polynomial.taylor r f).coeff n = (hasseDeriv n f).eval r := show (lcoeff R n).comp (Polynomial.taylor r) f = (leval r).comp (hasseDeriv n) f by
    congr 1; clear! f; ext i
    simp only [leval_apply, mul_one, one_mul, eval_monomial, LinearMap.comp_apply, map_sum,
      hasseDeriv_monomial, Polynomial.taylor_apply, monomial_comp, C_1, (commute_X (C r)).add_pow i]
    simp only [lcoeff_apply, ← C_eq_natCast, mul_assoc, ← C_pow, ← C_mul, coeff_mul_C,
      (Nat.cast_commute _ _).eq, coeff_X_pow, boole_mul, Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with h; · rfl
    push Not at h; rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, mul_zero]

