import Mathlib

variable {ι α M N : Type*}

variable [Monoid M]

theorem max_prod_le (l : List α) (f g : α → M) [LinearOrder M]
    [MulLeftMono M] [MulRightMono M] :
    max (l.map f).prod (l.map g).prod ≤ (l.map fun i ↦ max (f i) (g i)).prod := by
  rw [max_le_iff]
  constructor <;> apply List.prod_le_prod' <;> intros
  · apply le_max_left
  · apply le_max_right

