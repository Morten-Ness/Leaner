FAIL
import Mathlib

variable {ι : Type*}

theorem next_eq_self (c : ComplexShape ι) (j : ι) (hj : ¬c.Rel j (c.next j)) :
    c.next j = j := by
  classical
  by_cases h : c.next j = j
  · exact h
  · exfalso
    exact hj ((c.isCycle j).adj h)
