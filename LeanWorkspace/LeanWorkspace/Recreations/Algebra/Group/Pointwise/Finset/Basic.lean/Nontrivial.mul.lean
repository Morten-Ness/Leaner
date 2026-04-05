import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

theorem Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial := ht.mul_left hs.nonempty

