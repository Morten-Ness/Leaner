import Mathlib

variable {F α β : Type*}

variable {m n : ℕ}

theorem Odd.sub_odd (hm : Odd m) (hn : Odd n) : Even (m - n) := by grind

alias _root_.Odd.tsub_odd := Nat.Odd.sub_odd

