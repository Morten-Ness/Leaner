import Mathlib

variable {ι M M₀ : Type*}

theorem divisor_closure_eq_closure [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
    (x y : M₀) (hxy : x * y ∈ closure { r : M₀ | IsUnit r ∨ Prime r}) :
    x ∈ closure { r : M₀ | IsUnit r ∨ Prime r} := by
  obtain ⟨m, hm, hprod⟩ := exists_multiset_of_mem_closure hxy
  induction m using Multiset.induction generalizing x y with
  | empty =>
    apply subset_closure
    push _ ∈ _
    simp only [Multiset.prod_zero] at hprod
    left; exact .of_mul_eq_one _ hprod.symm
  | cons c s hind =>
    simp only [Multiset.mem_cons, forall_eq_or_imp, Set.mem_setOf] at hm
    simp only [Multiset.prod_cons] at hprod
    simp only [Set.mem_setOf_eq] at hind
    obtain ⟨ha₁ | ha₂, hs⟩ := hm
    · rcases ha₁.exists_right_inv with ⟨k, hk⟩
      refine hind x (y * k) ?_ hs ?_
      · simp only [← mul_assoc, ← hprod, ← Multiset.prod_cons, mul_comm]
        refine multiset_prod_mem _ _ (Multiset.forall_mem_cons.2 ⟨subset_closure ?_,
          Multiset.forall_mem_cons.2 ⟨subset_closure ?_, fun t ht => subset_closure (hs t ht)⟩⟩)
        · left; exact .of_mul_eq_one_right _ hk
        · left; exact ha₁
      · rw [← mul_one s.prod, ← hk, ← mul_assoc, ← mul_assoc, mul_eq_mul_right_iff, mul_comm]
        left; exact hprod
    · rcases ha₂.dvd_mul.1 (Dvd.intro _ hprod) with ⟨c, hc⟩ | ⟨c, hc⟩
      · rw [hc]; rw [hc, mul_assoc] at hprod
        refine Submonoid.mul_mem _ (subset_closure ?_)
          (hind _ _ ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod))
        · right; exact ha₂
        rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
        exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))
      rw [hc, mul_comm x _, mul_assoc, mul_comm c _] at hprod
      refine hind x c ?_ hs (mul_left_cancel₀ ha₂.ne_zero hprod)
      rw [← mul_left_cancel₀ ha₂.ne_zero hprod]
      exact multiset_prod_mem _ _ (fun t ht => subset_closure (hs t ht))

