import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem lcm_dvd {s : Multiset α} {a : α} : s.lcm ∣ a ↔ ∀ b ∈ s, b ∣ a := Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, lcm_dvd_iff])

