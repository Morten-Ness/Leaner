import Mathlib

variable {R S : Type*}

theorem List.trop_minimum [LinearOrder R] (l : List R) :
    trop l.minimum = List.sum (l.map (trop ∘ WithTop.some)) := by
  induction l with
  | nil => simp
  | cons hd tl IH => simp [List.minimum_cons, ← IH]

