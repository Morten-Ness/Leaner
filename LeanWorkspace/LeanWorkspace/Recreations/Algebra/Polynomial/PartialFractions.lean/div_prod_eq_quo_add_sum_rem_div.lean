import Mathlib

variable {R : Type*} [CommRing R]

variable (K : Type*) [Field K] [Algebra R[X] K] [FaithfulSMul R[X] K]

theorem div_prod_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
        ((↑f : K) / ∏ i ∈ s, ↑(g i)) = ↑q + ∑ i ∈ s, (r i : K) / (g i : K) := by
  have : Nontrivial R :=
    have : Nontrivial R[X] := Module.nontrivial R[X] K
    Module.nontrivial R R[X]
  have hgi (i : ι) (hi : i ∈ s) : (algebraMap R[X] K (g i))⁻¹ * algebraMap R[X] K (g i) = 1 :=
    inv_mul_cancel₀ (by simpa using (hg i hi).ne_zero)
  obtain ⟨q, r, hr, hf⟩ := Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    f hg hcop (fun _ => 1) hgi
  refine ⟨q, fun i => r i 0, fun i hi => hr i hi 0, ?_⟩
  simp_rw [Fin.sum_univ_one, Fin.val_zero, zero_add, pow_one, Finset.prod_inv_distrib] at hf
  simp_rw [Algebra.cast, div_eq_mul_inv]
  exact hf

