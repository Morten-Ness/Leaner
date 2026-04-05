import Mathlib

section

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ ∀ b ∈ s, a ∣ b := Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, dvd_gcd_iff])

end

section

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₂.gcd ∣ s₁.gcd := Multiset.dvd_gcd.2 fun _ hb ↦ Multiset.gcd_dvd (h hb)

end

section

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem gcd_ne_zero_iff (s : Multiset α) : s.gcd ≠ 0 ↔ ∃ x ∈ s, x ≠ 0 := by
  simp [Multiset.gcd_eq_zero_iff]

end

section

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm := Multiset.lcm_dvd.2 fun _ hb ↦ Multiset.dvd_lcm (h hb)

end
