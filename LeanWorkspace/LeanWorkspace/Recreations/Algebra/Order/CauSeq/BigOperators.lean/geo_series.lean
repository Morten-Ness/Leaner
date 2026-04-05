import Mathlib

variable {α β : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv]
  {f g : ℕ → β} {a : ℕ → α}

variable [Archimedean α]

theorem geo_series [Nontrivial β] (x : β) (hx1 : abv x < 1) :
    IsCauSeq abv fun n ↦ ∑ m ∈ range n, x ^ m := by
  have hx1' : abv x ≠ 1 := fun h ↦ by simp [h] at hx1
  refine IsCauSeq.of_abv ?_
  simp only [abv_pow abv, geom_sum_eq hx1']
  conv in _ / _ => rw [← neg_div_neg_eq, neg_sub, neg_sub]
  have : 0 < 1 - abv x := sub_pos.2 hx1
  refine IsCauSeq.of_mono_bounded _ (a := (1 : α) / (1 - abv x)) (m := 0) ?_ ?_
  · intro n _
    rw [abs_of_nonneg]
    · gcongr
      exact sub_le_self _ (abv_pow abv x n ▸ abv_nonneg _ _)
    refine div_nonneg (sub_nonneg.2 ?_) (sub_nonneg.2 <| le_of_lt hx1)
    exact pow_le_one₀ (by positivity) hx1.le
  · intro n _
    rw [← one_mul (abv x ^ n), pow_succ']
    gcongr

