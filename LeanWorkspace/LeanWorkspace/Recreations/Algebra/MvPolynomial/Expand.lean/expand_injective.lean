import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

theorem expand_injective {n : ℕ} (hn : 0 < n) : Function.Injective (MvPolynomial.expand n (R := R) (σ := σ)) :=
  fun g g' H => by
    ext d
    rw [← MvPolynomial.coeff_expand_smul _ (n.ne_zero_iff_zero_lt.mpr hn), H, MvPolynomial.coeff_expand_smul _
      (n.ne_zero_iff_zero_lt.mpr hn)]

