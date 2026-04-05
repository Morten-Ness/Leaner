import Mathlib

variable {R : Type*} [CommRing R]

variable {K : Type*} [CommRing K] [Algebra R[X] K]

theorem quo_add_sum_rem_mul_pow_inverse_unique [FaithfulSMul R[X] K] {ι : Type*}
    {s : Finset ι} {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    {n : ι → ℕ} {gi : ι → K} (hgi : ∀ i ∈ s, gi i * algebraMap R[X] K (g i) = 1)
    {q₁ q₂ : R[X]} {r₁ r₂ : (i : ι) → Fin (n i) → R[X]}
    (hr₁ : ∀ i ∈ s, ∀ j, (r₁ i j).degree < (g i).degree)
    (hr₂ : ∀ i ∈ s, ∀ j, (r₂ i j).degree < (g i).degree)
    (hf : algebraMap R[X] K q₁ + ∑ i ∈ s, ∑ j, algebraMap R[X] K (r₁ i j) * gi i ^ (j.1 + 1) =
      algebraMap R[X] K q₂ + ∑ i ∈ s, ∑ j, algebraMap R[X] K (r₂ i j) * gi i ^ (j.1 + 1)) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  classical
  suffices hff : ∀ {q : R[X]} {r : (i : ι) → Fin (n i) → R[X]},
      (algebraMap R[X] K q + ∑ i ∈ s, ∑ j,
        algebraMap R[X] K (r i j) * gi i ^ (j.1 + 1)) * ∏ i ∈ s, algebraMap R[X] K (g i) ^ n i =
      algebraMap R[X] K (q * ∏ i ∈ s, g i ^ n i + ∑ i ∈ s,
        ∑ j : Fin (n i), r i j.rev * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k) by
    apply_fun (· * ∏ i ∈ s, algebraMap R[X] K (g i) ^ n i) at hf
    rw [hff, hff, (FaithfulSMul.algebraMap_injective R[X] K).eq_iff] at hf
    obtain ⟨hq, hr⟩ := Polynomial.quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique hg hgg
      (fun i hi j => hr₁ i hi j.rev) (fun i hi j => hr₂ i hi j.rev) hf
    exact ⟨hq, fun i hi => funext fun j => j.rev_rev ▸ congrFun (hr i hi) j.rev⟩
  intro q r
  simp_rw [add_mul, Finset.sum_mul, map_add, map_sum, map_mul, map_prod, map_pow]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i hi => ?_)
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans (Fintype.sum_congr _ _ fun j => ?_)
  rw [Fin.revPerm_apply, ← Finset.mul_prod_erase s _ hi, ← mul_assoc,
    mul_assoc (algebraMap R[X] K (r i j.rev))]
  refine congrArg (algebraMap R[X] K (r i j.rev) * · * _) ?_
  rw [← mul_one (gi i ^ (j.rev.1 + 1)), ← @one_pow K _ j, ← hgi i hi,
    mul_pow, ← mul_assoc, ← pow_add, Fin.val_rev, Nat.add_right_comm, Nat.add_assoc,
    Nat.sub_add_cancel (by lia), mul_right_comm, ← mul_pow, hgi i hi, one_pow, one_mul]

