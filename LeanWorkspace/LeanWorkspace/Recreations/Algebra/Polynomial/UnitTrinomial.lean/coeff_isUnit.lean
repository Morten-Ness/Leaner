import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem coeff_isUnit (hp : p.IsUnitTrinomial) {k : ℕ} (hk : k ∈ p.support) :
    IsUnit (p.coeff k) := by
  obtain ⟨k, m, n, hkm, hmn, u, v, w, rfl⟩ := hp
  have := support_trinomial' k m n (u : ℤ) v w hk
  rw [mem_insert, mem_insert, mem_singleton] at this
  rcases this with (rfl | rfl | rfl)
  · refine ⟨u, by rw [Polynomial.trinomial_trailing_coeff' hkm hmn]⟩
  · refine ⟨v, by rw [Polynomial.trinomial_middle_coeff hkm hmn]⟩
  · refine ⟨w, by rw [Polynomial.trinomial_leading_coeff' hkm hmn]⟩

