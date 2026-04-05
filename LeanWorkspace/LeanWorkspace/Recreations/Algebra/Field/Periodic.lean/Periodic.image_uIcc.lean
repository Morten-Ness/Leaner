import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Periodic.image_uIcc [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    [Archimedean α] (h : Periodic f c)
    (hc : c ≠ 0) (a : α) : f '' uIcc a (a + c) = Set.range f := by
  cases hc.lt_or_gt with
  | inl hc =>
    rw [uIcc_of_ge (add_le_of_nonpos_right hc.le), ← h.neg.image_Icc (neg_pos.2 hc) (a + c),
      add_neg_cancel_right]
  | inr hc => rw [uIcc_of_le (le_add_of_nonneg_right hc.le), h.image_Icc hc]

