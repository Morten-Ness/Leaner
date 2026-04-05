import Mathlib

variable {R S : Type*}

theorem List.untrop_prod [AddMonoid R] (l : List (Tropical R)) :
    untrop l.prod = List.sum (l.map untrop) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [← IH]

