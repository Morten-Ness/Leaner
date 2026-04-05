import Mathlib

variable {ι M M₀ : Type*}

theorem Multiset.prod_primes_dvd [CommMonoidWithZero M₀] [IsCancelMulZero M₀]
    [∀ a : M₀, DecidablePred (Associated a)] {s : Multiset M₀} (n : M₀) (h : ∀ a ∈ s, Prime a)
    (div : ∀ a ∈ s, a ∣ n) (uniq : ∀ a, s.countP (Associated a) ≤ 1) : s.prod ∣ n := by
  induction s using Multiset.induction_on generalizing n with
  | empty => simp only [Multiset.prod_zero, one_dvd]
  | cons a s induct =>
    rw [Multiset.prod_cons]
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    gcongr
    refine induct _ (fun a ha => h a (Multiset.mem_cons_of_mem ha)) (fun b b_in_s => ?_)
      fun a => (Multiset.countP_le_of_le _ (Multiset.le_cons_self _ _)).trans (uniq a)
    have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
    have a_prime := h a (Multiset.mem_cons_self a s)
    have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
    refine (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => ?_
    have assoc := b_prime.associated_of_dvd a_prime b_div_a
    have := uniq a
    rw [Multiset.countP_cons_of_pos _ (Associated.refl _), Nat.succ_le_succ_iff, ← not_lt,
      Multiset.countP_pos] at this
    exact this ⟨b, b_in_s, assoc.symm⟩

