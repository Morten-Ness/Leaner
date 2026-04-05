import Mathlib

variable {ι M M₀ : Type*}

theorem Finset.prod_primes_dvd [CommMonoidWithZero M₀] [IsCancelMulZero M₀] [Subsingleton M₀ˣ]
    {s : Finset M₀} (n : M₀) (h : ∀ a ∈ s, Prime a) (div : ∀ a ∈ s, a ∣ n) : ∏ p ∈ s, p ∣ n := by
  classical
    exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countP_eq_card_filter,
            ← s.val.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup])

