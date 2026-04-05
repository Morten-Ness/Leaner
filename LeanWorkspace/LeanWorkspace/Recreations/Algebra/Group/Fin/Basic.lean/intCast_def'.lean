import Mathlib

open scoped Fin.NatCast Fin.IntCast

variable {n : ℕ}

theorem intCast_def' {n : Nat} [NeZero n] (x : Int) :
    (x : Fin n) = if 0 ≤ x then ↑x.natAbs else -↑x.natAbs := Fin.intCast_def _

