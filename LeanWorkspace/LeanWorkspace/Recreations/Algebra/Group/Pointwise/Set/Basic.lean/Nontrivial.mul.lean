import Mathlib

variable {F α β γ : Type*}

variable [Mul α] [IsLeftCancelMul α] {s t : Set α}

theorem Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial := ht.mul_left hs.nonempty

