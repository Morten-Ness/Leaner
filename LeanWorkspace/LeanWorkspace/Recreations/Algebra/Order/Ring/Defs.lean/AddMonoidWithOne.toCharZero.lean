import Mathlib

variable {R : Type u}

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

theorem AddMonoidWithOne.toCharZero {R}
    [AddMonoidWithOne R] [PartialOrder R] [ZeroLEOneClass R]
    [NeZero (1 : R)] [AddLeftStrictMono R] : CharZero R where
  cast_injective := (strictMono_nat_of_lt_succ fun n ↦ by rw [Nat.cast_succ]; apply lt_add_one).injective

-- see Note [lower instance priority]

