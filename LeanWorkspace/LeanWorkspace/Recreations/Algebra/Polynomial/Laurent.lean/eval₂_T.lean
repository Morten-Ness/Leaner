import Mathlib

variable {R S : Type*}

variable [CommSemiring R] {S : Type*} [CommSemiring S] (f : R →+* S) (x : Sˣ)

theorem eval₂_T (n : ℤ) : LaurentPolynomial.eval₂ f x (LaurentPolynomial.T n) = (x ^ n).val := by
  by_cases! hn : 0 ≤ n
  · lift n to ℕ using hn
    apply LaurentPolynomial.eval₂_T_n
  · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [LaurentPolynomial.eval₂_T_neg_n, zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]

