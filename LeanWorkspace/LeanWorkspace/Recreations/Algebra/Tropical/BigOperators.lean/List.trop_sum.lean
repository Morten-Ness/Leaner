import Mathlib

variable {R S : Type*}

theorem List.trop_sum [AddMonoid R] (l : List R) : trop l.sum = List.prod (l.map trop) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]

