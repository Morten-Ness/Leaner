import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R]
    (a : R) : 0 ≤ a * a := by simpa only [sq] using sq_nonneg a

