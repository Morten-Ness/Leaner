import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem le_iff_forall_one_lt_le_mul₀ {α : Type*}
    [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} (hb : 0 ≤ b) : a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε := by
  refine ⟨fun h _ hε ↦ h.trans <| le_mul_of_one_le_right hb hε.le, fun h ↦ ?_⟩
  obtain rfl | hb := hb.eq_or_lt
  · simp_rw [zero_mul] at h
    exact h 2 one_lt_two
  refine le_of_forall_gt_imp_ge_of_dense fun x hbx => ?_
  convert h (x / b) ((one_lt_div hb).mpr hbx)
  rw [mul_div_cancel₀ _ hb.ne']

