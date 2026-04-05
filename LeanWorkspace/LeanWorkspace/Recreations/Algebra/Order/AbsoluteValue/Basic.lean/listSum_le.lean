import Mathlib

variable {ι α R S : Type*}

variable {R S : Type*} [Semiring R] [Semiring S] [PartialOrder S] (abv : AbsoluteValue R S)

theorem listSum_le [AddLeftMono S] (l : List R) : abv l.sum ≤ (l.map abv).sum := by
  induction l with
  | nil => simp
  | cons head tail ih => exact (AbsoluteValue.add_le abv ..).trans <| add_le_add_right ih (abv head)

