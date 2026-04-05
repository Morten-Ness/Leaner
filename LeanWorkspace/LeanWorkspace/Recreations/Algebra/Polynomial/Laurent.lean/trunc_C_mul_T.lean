import Mathlib

variable {R S : Type*}

variable [Semiring R]

theorem trunc_C_mul_T (n : ℤ) (r : R) : LaurentPolynomial.trunc (Polynomial.C r * LaurentPolynomial.T n) = ite (0 ≤ n) (monomial n.toNat r) 0 := by
  apply (toFinsuppIso R).injective
  simp only [← LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.trunc, AddMonoidHom.coe_comp, Function.comp_apply,
    RingHom.toAddMonoidHom_eq_coe, RingEquiv.toRingHom_eq_coe, Int.ofNat_eq_natCast,
    AddMonoidHom.coe_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, toFinsuppIso_apply]
  -- We need `erw` to see through the identification of `Finsupp` with `LaurentSeries`.
  erw [comapDomain.addMonoidHom_apply Int.ofNat_injective]
  split_ifs with n0
  · rw [toFinsupp_monomial]
    lift n to ℕ using n0
    apply comapDomain_single
  · rw [toFinsupp_inj]
    ext a
    have : a ≠ n := by lia
    simp only [coeff_ofFinsupp, comapDomain_apply, Int.ofNat_eq_natCast, Polynomial.coeff_zero,
      single_eq_of_ne this]

