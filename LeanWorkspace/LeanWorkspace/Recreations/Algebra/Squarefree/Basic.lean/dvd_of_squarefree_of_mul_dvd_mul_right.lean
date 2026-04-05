import Mathlib

variable {R : Type*}

variable [CommMonoidWithZero R] [IsCancelMulZero R] {x y p d : R}

variable [DecompositionMonoid R]

theorem dvd_of_squarefree_of_mul_dvd_mul_right (hx : Squarefree x) (h : d * d ∣ x * y) : d ∣ y := by
  nontriviality R
  obtain ⟨a, b, ha, hb, eq⟩ := exists_dvd_and_dvd_of_dvd_mul h
  replace ha : Squarefree a := hx.squarefree_of_dvd ha
  obtain ⟨c, hc⟩ : a ∣ d := ha.isRadical 2 d ⟨b, by rw [sq, eq]⟩
  rw [hc, mul_assoc, (mul_right_injective₀ ha.ne_zero).eq_iff] at eq
  exact dvd_trans ⟨c, by rw [hc, ← eq, mul_comm]⟩ hb

