import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem extract_gcd' (s t : Multiset α) (hs : ∃ x, x ∈ s ∧ x ≠ (0 : α))
    (ht : s = t.map (s.gcd * ·)) : t.gcd = 1 := ((mul_right_eq_self₀ (a := s.gcd)).1 <| by
      conv_lhs => rw [← Multiset.normalize_gcd, ← Multiset.gcd_map_mul, ← ht]).resolve_right <| by
    contrapose! hs
    exact Multiset.gcd_eq_zero_iff s.1 hs

