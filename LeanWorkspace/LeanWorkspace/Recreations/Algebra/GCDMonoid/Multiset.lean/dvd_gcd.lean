import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

theorem dvd_gcd {s : Multiset α} {a : α} : a ∣ s.gcd ↔ ∀ b ∈ s, a ∣ b := Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and, dvd_gcd_iff])

