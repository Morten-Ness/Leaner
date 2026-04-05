import Mathlib

variable {R : Type*} [CommRing R]

theorem quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) {n : ι → ℕ}
    {q₁ q₂ : R[X]} {r₁ r₂ : (i : ι) → Fin (n i) → R[X]}
    (hr₁ : ∀ i ∈ s, ∀ j, (r₁ i j).degree < (g i).degree)
    (hr₂ : ∀ i ∈ s, ∀ j, (r₂ i j).degree < (g i).degree)
    (hf : q₁ * (∏ i ∈ s, g i ^ n i) +
        ∑ i ∈ s, ∑ j, r₁ i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k =
      q₂ * (∏ i ∈ s, g i ^ n i) +
        ∑ i ∈ s, ∑ j, r₂ i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  nontriviality R
  simp only [← Finset.sum_mul] at hf
  have hrd {r : (i : ι) → Fin (n i) → R[X]} (hr : ∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree)
      (i : ι) (hi : i ∈ s) : (∑ j, r i j * g i ^ j.1).degree < (g i ^ n i).degree := by
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 fun j _ => ?_)
    · rw [bot_lt_iff_ne_bot, degree_ne_bot]
      exact ((hg i hi).pow (n i)).ne_zero
    · refine (degree_mul_le _ _).trans_lt ?_
      rw [degree_eq_natDegree ((hg i hi).pow j.1).ne_zero, (hg i hi).natDegree_pow,
        degree_eq_natDegree ((hg i hi).pow (n i)).ne_zero, (hg i hi).natDegree_pow]
      conv_rhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 j.neZero.ne)]
      rw [Nat.add_one_mul, Nat.add_comm, Nat.cast_add, ← degree_eq_natDegree (hg i hi).ne_zero]
      refine WithBot.add_lt_add_of_lt_of_le (WithBot.natCast_ne_bot _) (hr i hi j) ?_
      exact Nat.cast_le.2 (Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt j.isLt))
  obtain ⟨hq, hr⟩ := Polynomial.quo_mul_prod_add_sum_rem_mul_prod_unique
    (fun i hi => (hg i hi).pow (n i)) (hgg.imp fun i j hij => hij.pow) (hrd hr₁) (hrd hr₂) hf
  refine ⟨hq, fun i hi => ?_⟩
  exact (Polynomial.quo_mul_pow_add_sum_rem_mul_pow_unique (hg i hi) (hr₁ i hi) (hr₂ i hi)
    (congrArg (0 * g i ^ n i + ·) (hr i hi))).2

