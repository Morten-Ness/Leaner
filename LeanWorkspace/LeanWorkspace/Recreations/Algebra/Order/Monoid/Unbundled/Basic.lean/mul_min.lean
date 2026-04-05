import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LinearOrder α] {a b c d : α}

theorem mul_min [MulLeftMono α] (a b c : α) :
    a * min b c = min (a * b) (a * c) := mul_right_mono.map_min

