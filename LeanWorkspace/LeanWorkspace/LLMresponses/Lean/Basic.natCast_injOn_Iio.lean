FAIL
import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

variable [IsRightCancelAdd R]

theorem natCast_injOn_Iio : (Set.Iio p).InjOn ((↑) : ℕ → R) := by
  intro a ha b hb hab
  have h1 : a % p = b % p := by
    simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using (CharP.cast_eq_zero_iff (R := R) p (a - b))
  have hcast : ((a : R) - (b : R)) = 0 := by
    sorry
  omega
