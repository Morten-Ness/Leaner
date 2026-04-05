import Mathlib

variable {α : Type u}

theorem tail_mul (x y : FreeSemigroup α) : (x * y).2 = x.2 ++ y.1 :: y.2 := rfl

