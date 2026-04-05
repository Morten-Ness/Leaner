import Mathlib

variable {R : Type*} [CommRing R]

theorem quo_mul_prod_add_sum_rem_mul_prod_unique {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    {q₁ q₂ : R[X]} {r₁ r₂ : ι → R[X]}
    (hr₁ : ∀ i ∈ s, (r₁ i).degree < (g i).degree) (hr₂ : ∀ i ∈ s, (r₂ i).degree < (g i).degree)
    (hf : q₁ * (∏ i ∈ s, g i) + ∑ i ∈ s, r₁ i * (∏ k ∈ s.erase i, g k) =
      q₂ * (∏ i ∈ s, g i) + ∑ i ∈ s, r₂ i * (∏ k ∈ s.erase i, g k)) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  induction s using Finset.cons_induction with
  | empty => simpa using hf
  | cons i s hi ih =>
    rw [Finset.forall_mem_cons] at hg hr₁ hr₂
    have cop : IsCoprime (g i) (∏ i ∈ s, g i) := by
      clear *-hgg
      induction s using Finset.cons_induction with
      | empty => simp [isCoprime_one_right]
      | cons j s hj ih =>
        rw [Finset.prod_cons, IsCoprime.mul_right_iff]
        refine ⟨hgg (by simp) (by simp) fun hij => hi (by simp [hij]), ih ?_ ?_⟩
        · exact mt Finset.mem_cons_of_mem hi
        · exact hgg.mono (SetLike.coe_mono (Finset.cons_subset_cons.2 (Finset.subset_cons hj)))
    rw [Finset.prod_cons, Finset.sum_cons, Finset.sum_cons, Finset.erase_cons] at hf
    have hjs {j : ι} (hj : j ∈ s) : i ≠ j := fun hij => hi (hij ▸ hj)
    simp +contextual only [Finset.erase_cons_of_ne hi (hjs _),
      Finset.prod_cons, ← mul_left_comm (g i), ← Finset.mul_sum] at hf
    rw [add_left_comm, ← mul_add, add_left_comm, ← mul_add] at hf
    rw [← sub_eq_zero, add_sub_add_comm, ← sub_mul, ← mul_sub,
      ← neg_sub, neg_mul, neg_add_eq_sub, sub_eq_zero] at hf
    have hgid : g i ∣ r₂ i - r₁ i := cop.dvd_of_dvd_mul_right (hf ▸ dvd_mul_right _ _)
    rw [add_sub_add_comm, ← sub_mul, mul_add, ← mul_assoc,
      ← eq_sub_iff_add_eq', ← sub_mul, ← Finset.sum_sub_distrib] at hf
    simp only [← sub_mul] at hf
    have hpgd : ∏ i ∈ s, g i ∣ _ := cop.symm.dvd_of_dvd_mul_left (hf.symm ▸ dvd_mul_left _ _)
    have hdr : (r₂ i - r₁ i).degree < (g i).degree :=
      (degree_sub_le (r₂ i) (r₁ i)).trans_lt (max_lt hr₂.1 hr₁.1)
    have hr0 : r₂ i - r₁ i = 0 := (hg.1.not_dvd_of_degree_lt · hdr).mtr hgid
    have hpm : (∏ i ∈ s, g i).Monic := monic_prod_of_monic s g hg.2
    have hdp : (∑ i ∈ s, (r₁ i - r₂ i) * ∏ k ∈ s.erase i, g k).degree < (∏ i ∈ s, g i).degree := by
      refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 ?_)
      · rw [bot_lt_iff_ne_bot, degree_ne_bot]
        exact hpm.ne_zero_of_polynomial_ne fun h : r₂ i - r₁ i = g i => lt_irrefl _ (h ▸ hdr)
      · intro j hj
        rw [← Finset.mul_prod_erase s g hj, mul_comm (g j), (hg.2 j hj).degree_mul]
        refine (degree_mul_le (r₁ j - r₂ j) (∏ k ∈ s.erase j, g k)).trans_lt ?_
        have dnb : (∏ k ∈ s.erase j, g k).degree ≠ ⊥ := by
          rw [degree_ne_bot]
          exact (monic_prod_of_monic _ g
            fun j hj => hg.2 j (Finset.mem_of_mem_erase hj)).ne_zero_of_polynomial_ne
            fun h : r₂ i - r₁ i = g i => lt_irrefl _ (h ▸ hdr)
        rw [add_comm, WithBot.add_lt_add_iff_left dnb]
        exact (degree_sub_le (r₁ j) (r₂ j)).trans_lt (max_lt (hr₁.2 j hj) (hr₂.2 j hj))
    have hp0 : ∑ i ∈ s, (r₁ i - r₂ i) * ∏ k ∈ s.erase i, g k = 0 :=
      (hpm.not_dvd_of_degree_lt · hdp).mtr hpgd
    rw [hr0, hp0, mul_zero, zero_sub, neg_mul, eq_comm, neg_eq_zero,
      ← mul_rotate, (hpm.mul hg.1).mul_right_eq_zero_iff] at hf
    simp only [sub_mul, Finset.sum_sub_distrib] at hp0
    rw [sub_eq_zero] at hf hr0 hp0
    obtain ⟨-, hrr⟩ := ih hg.2 (hgg.mono (SetLike.coe_mono (Finset.subset_cons hi)))
      hr₁.2 hr₂.2 congr($hf * ∏ i ∈ s, g i + $hp0)
    exact ⟨hf, (Finset.forall_mem_cons hi (fun j => r₁ j = r₂ j)).2 ⟨hr0.symm, hrr⟩⟩

