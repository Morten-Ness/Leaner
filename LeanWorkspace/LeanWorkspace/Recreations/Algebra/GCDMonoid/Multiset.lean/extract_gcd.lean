import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem extract_gcd (s : Multiset α) (hs : s ≠ 0) :
    ∃ t : Multiset α, s = t.map (s.gcd * ·) ∧ t.gcd = 1 := by
  classical
    by_cases! h : ∀ x ∈ s, x = (0 : α)
    · use replicate (card s) 1
      rw [map_replicate, eq_replicate, mul_one, Multiset.gcd_eq_zero_iff s.2 h, ← nsmul_singleton,
    ← Multiset.gcd_dedup, dedup_nsmul (card_pos.2 hs).ne', dedup_singleton, Multiset.gcd_singleton]
      exact ⟨⟨rfl, h⟩, normalize_one⟩
    · choose f hf using @Multiset.gcd_dvd _ _ _ s
      refine ⟨s.pmap @f fun _ ↦ id, ?_, Multiset.extract_gcd' s _ h ?_⟩ <;>
      · rw [map_pmap]
        conv_lhs => rw [← s.map_id, ← s.pmap_eq_map _ _ fun _ ↦ id]
        congr with (x hx)
        rw [id, ← hf hx]

