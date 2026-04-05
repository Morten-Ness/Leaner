import Mathlib

variable {ι α R S : Type*}

variable [Field R] [Semifield S] [LinearOrder S] [IsStrictOrderedRing S] [ExistsAddOfLE S]
  {v : AbsoluteValue R S}

theorem IsNontrivial.exists_abv_lt_one (h : v.IsNontrivial) : ∃ x ≠ 0, v x < 1 := by
  obtain ⟨y, hy⟩ := h.exists_abv_gt_one
  have hy₀ := AbsoluteValue.ne_zero_iff v.mp <| (zero_lt_one.trans hy).ne'
  refine ⟨y⁻¹, inv_ne_zero hy₀, ?_⟩
  rw [map_inv₀]
  exact (inv_lt_one₀ <| v.pos hy₀).mpr hy

