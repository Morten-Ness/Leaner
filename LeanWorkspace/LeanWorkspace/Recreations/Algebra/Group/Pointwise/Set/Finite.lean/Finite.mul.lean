import Mathlib

variable {F α β γ : Type*}

variable [Mul α] {s t : Set α}

theorem Finite.mul : s.Finite → t.Finite → (s * t).Finite := Finite.image2 _

