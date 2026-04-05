import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_insert [DecidableEq β] {b : β} :
    (insert b s : Finset β).gcd f = GCDMonoid.gcd (f b) (s.gcd f) := by
  by_cases h : b ∈ s
  · rw [insert_eq_of_mem h,
      (gcd_eq_right_iff (f b) (s.gcd f) (Multiset.normalize_gcd (s.1.map f))).2 (Finset.gcd_dvd h)]
  apply fold_insert h

