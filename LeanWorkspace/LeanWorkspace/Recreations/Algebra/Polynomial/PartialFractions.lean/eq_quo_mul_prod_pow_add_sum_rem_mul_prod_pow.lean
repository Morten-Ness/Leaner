import Mathlib

variable {R : Type*} [CommRing R]

theorem eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow [Nontrivial R] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) (n : ι → ℕ) :
    ∃ (q : R[X]) (r : (i : ι) → Fin (n i) → R[X]),
      (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      f = q * (∏ i ∈ s, g i ^ n i) +
        ∑ i ∈ s, ∑ j, r i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k := by
  obtain ⟨q, r, -, hf⟩ := Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod f
    (fun i hi => (hg i hi).pow (n i))
    (hgg.mono' fun i j hij => hij.pow)
  have hc (i : ι) : ∃ (q' : R[X]) (r' : Fin (n i) → R[X]), i ∈ s →
      (∀ j, (r' j).degree < (g i).degree) ∧
      r i = q' * g i ^ (n i) + ∑ j, r' j * g i ^ j.1 :=
    if hi : i ∈ s then
      (Polynomial.eq_quo_mul_pow_add_sum_rem_mul_pow (r i) (hg i hi) (n i)).elim
        fun q' h => h.elim fun r' h => ⟨q', r', fun _ => h⟩
    else
      ⟨0, fun _ => 0, hi.elim⟩
  choose q' r' hr' hr using hc
  refine ⟨q + ∑ i ∈ s, q' i, r', hr', hf.trans ?_⟩
  rw [add_mul, add_assoc, add_right_inj, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.mul_prod_erase s _ hi, hr i hi, add_mul, Finset.sum_mul, mul_assoc]

