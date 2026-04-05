import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem IsLUB.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsLUB s b) :
    IsLUB ((fun b => a * b) '' s) (a * b) := by
  obtain ha | rfl := ha.lt_or_eq
  · exact (OrderIso.mulLeft₀ _ ha).isLUB_image'.2 hs
  · simp_rw [zero_mul]
    obtain rfl | ne := s.eq_empty_or_nonempty
    · simp only [Set.image_empty, isLUB_empty_iff] at hs ⊢
      have hb := hs (b + b)
      rw [le_add_iff_nonneg_right] at hb
      exact hs.mono hb
    rw [ne.image_const]
    exact isLUB_singleton

