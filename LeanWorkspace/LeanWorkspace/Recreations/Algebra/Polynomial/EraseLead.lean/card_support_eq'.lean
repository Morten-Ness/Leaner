import Mathlib

variable {R : Type*} [Semiring R] {f : R[X]}

theorem card_support_eq' {n : ℕ} (k : Fin n → ℕ) (x : Fin n → R) (hk : Function.Injective k)
    (hx : ∀ i, x i ≠ 0) : #(∑ i, Polynomial.C (x i) * Polynomial.X ^ k i).support = n := by
  suffices (∑ i, Polynomial.C (x i) * Polynomial.X ^ k i).support = image k Finset.univ by
    rw [this, Finset.univ.card_image_of_injective hk, card_fin]
  simp_rw [Finset.ext_iff, mem_support_iff, finset_sum_coeff, coeff_C_mul_X_pow, mem_image,
    Finset.mem_univ, true_and]
  refine fun i => ⟨fun h => ?_, ?_⟩
  · obtain ⟨j, _, h⟩ := exists_ne_zero_of_sum_ne_zero h
    exact ⟨j, (ite_ne_right_iff.mp h).1.symm⟩
  · rintro ⟨j, _, rfl⟩
    rw [sum_eq_single_of_mem j (Finset.mem_univ j), if_pos rfl]
    · exact hx j
    · exact fun m _ hmj => if_neg fun h => hmj.symm (hk h)

