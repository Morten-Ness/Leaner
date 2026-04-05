import Mathlib

variable {α : Type*} [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable [DecidableEq α]

theorem lcm_dedup (s : Multiset α) : (dedup s).lcm = s.lcm := Multiset.induction_on s (by simp) fun a s IH ↦ by
    by_cases h : a ∈ s; swap; · simp [IH, h]
    simp only [h, dedup_cons_of_mem, IH, Multiset.lcm_cons]
    unfold Multiset.lcm
    rw [← cons_erase h, fold_cons_left, ← lcm_assoc, lcm_same]
    apply lcm_eq_of_associated_left (associated_normalize _)

