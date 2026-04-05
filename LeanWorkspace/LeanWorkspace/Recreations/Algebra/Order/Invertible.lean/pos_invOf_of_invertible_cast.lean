import Mathlib

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a : R}

theorem pos_invOf_of_invertible_cast [Nontrivial R] (n : ℕ)
    [Invertible (n : R)] : 0 < ⅟(n : R) := invOf_pos.2 <| Nat.cast_pos.2 <| pos_of_invertible_cast (R := R) n

