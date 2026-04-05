import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

variable [IsRightCancelAdd R]

theorem natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : ℕ → R) := fun _a ha _b hb hab ↦ ((CharP.natCast_eq_natCast _ _).1 hab).eq_of_lt_of_lt ha hb

