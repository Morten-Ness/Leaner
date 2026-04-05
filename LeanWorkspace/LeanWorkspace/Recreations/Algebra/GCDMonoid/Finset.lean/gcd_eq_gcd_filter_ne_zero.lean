import Mathlib

variable {ι α β γ : Type*}

variable [CommMonoidWithZero α] [NormalizedGCDMonoid α]

variable {s s₁ s₂ : Finset β} {f : β → α}

theorem gcd_eq_gcd_filter_ne_zero [DecidablePred fun x : β ↦ f x = 0] :
    s.gcd f = {x ∈ s | f x ≠ 0}.gcd f := by
  classical
    trans ({x ∈ s | f x = 0} ∪ {x ∈ s | f x ≠ 0}).gcd f
    · rw [filter_union_filter_not_eq]
    rw [Finset.gcd_union]
    refine Eq.trans (?_ : _ = GCDMonoid.gcd (0 : α) ?_) (?_ : GCDMonoid.gcd (0 : α) _ = _)
    · exact Finset.gcd {x ∈ s | f x ≠ 0} f
    · refine congr (congr rfl <| s.induction_on ?_ ?_) (by simp)
      · simp
      · intro a s _ h
        rw [filter_insert]
        split_ifs with h1 <;> simp [h, h1]
    simp only [gcd_zero_left, Finset.normalize_gcd]

nonrec theorem gcd_mul_left {a : α} : (s.gcd fun x ↦ a * f x) = normalize a * s.gcd f := by
  classical
    refine s.induction_on ?_ ?_
    · simp
    · intro b t _ h
      rw [Finset.gcd_insert, Finset.gcd_insert, h, ← gcd_mul_left]
      apply ((normalize_associated a).mul_right _).gcd_eq_right

nonrec theorem gcd_mul_right {a : α} : (s.gcd fun x ↦ f x * a) = s.gcd f * normalize a := by
  classical
    refine s.induction_on ?_ ?_
    · simp
    · intro b t _ h
      rw [Finset.gcd_insert, Finset.gcd_insert, h, ← gcd_mul_right]
      apply ((normalize_associated a).mul_left _).gcd_eq_right

