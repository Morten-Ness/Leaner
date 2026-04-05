import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable [DecidableEq α]

theorem gcd_dedup (s : Multiset α) : (dedup s).gcd = s.gcd := Multiset.induction_on s (by simp) fun a s IH ↦ by
    by_cases h : a ∈ s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, Multiset.gcd_cons]
    unfold Multiset.gcd
    rw [← cons_erase h, fold_cons_left, ← gcd_assoc, gcd_same]
    apply (associated_normalize _).gcd_eq_left

