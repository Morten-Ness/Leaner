import Mathlib

variable {α β : Type*}

variable [Mul α]

variable [LinearOrder α] {a b c d : α}

theorem mul_max [MulLeftMono α] (a b c : α) :
    a * max b c = max (a * b) (a * c) := mul_right_mono.map_max

