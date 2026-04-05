import Mathlib

variable {ι : Type*}

theorem next_eq_self (c : ComplexShape ι) (j : ι) (hj : ¬c.Rel j (c.next j)) :
    c.next j = j := ComplexShape.next_eq_self' c j (fun k hk' => hj (by simpa only [ComplexShape.next_eq' c hk'] using hk'))

