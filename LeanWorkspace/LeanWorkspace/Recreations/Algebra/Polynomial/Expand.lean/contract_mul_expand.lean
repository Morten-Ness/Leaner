import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem contract_mul_expand {p : ℕ} (hp : p ≠ 0) (f g : R[X]) :
    Polynomial.contract p (f * Polynomial.expand R p g) = Polynomial.contract p f * g := by
  ext n
  rw [Polynomial.coeff_contract hp, coeff_mul, coeff_mul, ← sum_subset
    (s₁ := (antidiagonal n).image fun x ↦ (x.1 * p, x.2 * p)), sum_image]
  · simp_rw [Polynomial.coeff_expand_mul hp.bot_lt, Polynomial.coeff_contract hp]
  · intro x hx y hy eq; simpa only [Prod.ext_iff, Nat.mul_right_cancel_iff hp.bot_lt] using eq
  · simp_rw [subset_iff, mem_image, mem_antidiagonal]; rintro _ ⟨x, rfl, rfl⟩; simp_rw [add_mul]
  simp_rw [mem_image, mem_antidiagonal]
  intro ⟨x, y⟩ eq nex
  by_cases h : p ∣ y
  · obtain ⟨x, rfl⟩ : p ∣ x := (Nat.dvd_add_iff_left h).mpr (eq ▸ dvd_mul_left p n)
    obtain ⟨y, rfl⟩ := h
    refine (nex ⟨⟨x, y⟩, (Nat.mul_right_cancel_iff hp.bot_lt).mp ?_, by simp_rw [mul_comm]⟩).elim
    rw [← eq, mul_comm, mul_add]
  · rw [Polynomial.coeff_expand hp.bot_lt, if_neg h, mul_zero]

