import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem prod_min_le [LinearOrder M] [MulLeftMono M]
    [MulRightMono M] (l : List α) (f g : α → M) :
    (l.map fun i ↦ min (f i) (g i)).prod ≤ min (l.map f).prod (l.map g).prod := by
  rw [le_min_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply min_le_left
  · apply min_le_right

