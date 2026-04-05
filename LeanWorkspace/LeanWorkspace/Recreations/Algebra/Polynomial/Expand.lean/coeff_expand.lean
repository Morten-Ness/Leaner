import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem coeff_expand {p : ℕ} (hp : 0 < p) (f : R[X]) (n : ℕ) :
    (Polynomial.expand R p f).coeff n = if p ∣ n then f.coeff (n / p) else 0 := by
  simp only [Polynomial.expand_eq_sum]
  simp_rw [coeff_sum, ← pow_mul, C_mul_X_pow_eq_monomial, coeff_monomial, sum]
  split_ifs with h
  · rw [Finset.sum_eq_single (n / p), Nat.mul_div_cancel' h, if_pos rfl]
    · intro b _ hb2
      rw [if_neg]
      intro hb3
      apply hb2
      rw [← hb3, Nat.mul_div_cancel_left b hp]
    · intro hn
      rw [notMem_support_iff.1 hn]
      split_ifs <;> rfl
  · rw [Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    exact fun hkn => h ⟨k, hkn.symm⟩

