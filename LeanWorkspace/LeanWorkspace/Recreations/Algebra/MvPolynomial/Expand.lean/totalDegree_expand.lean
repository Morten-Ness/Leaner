import Mathlib

variable {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] (p : ℕ)

variable {p} (φ : MvPolynomial σ R)

theorem totalDegree_expand (f : MvPolynomial σ R) :
    (MvPolynomial.expand p f).totalDegree = f.totalDegree * p := by
  classical
  rcases p.eq_zero_or_pos with hp | hp
  · simp [hp]
  by_cases hf : f = 0
  · rw [hf, map_zero, totalDegree_zero, zero_mul]
  simp_rw [totalDegree_eq, MvPolynomial.support_expand _ (p.ne_zero_iff_zero_lt.mpr hp)]
  simp only [Finsupp.card_toMultiset, Finset.sup_image, Finset.sup_mul₀, Function.comp_def]
  congr! 2 with d
  rw [Finsupp.sum_of_support_subset _ Finsupp.support_smul _ (by simp)]
  simp [Finsupp.sum, Finset.sum_mul, mul_comm p]

