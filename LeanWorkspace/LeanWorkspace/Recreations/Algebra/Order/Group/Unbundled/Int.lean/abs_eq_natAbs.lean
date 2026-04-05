import Mathlib

theorem abs_eq_natAbs : ∀ a : ℤ, |a| = natAbs a
  | (n : ℕ) => abs_of_nonneg <| natCast_nonneg _
  | -[_+1] => abs_of_nonpos <| le_of_lt <| negSucc_lt_zero _
