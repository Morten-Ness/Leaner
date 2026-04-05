import Mathlib

variable {ι : Type*}

theorem next_eq_self' (c : ComplexShape ι) (j : ι) (hj : ∀ k, ¬c.Rel j k) :
    c.next j = j := dif_neg (by simpa using hj)

