import Mathlib

theorem ediv_eq_zero_of_lt_abs {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < |b|) : a / b = 0 := match b, |b|, Int.abs_eq_natAbs b, H2 with
  | (n : ℕ), _, rfl, H2 => ediv_eq_zero_of_lt H1 H2
  | -[n+1], _, rfl, H2 => neg_injective <| by rw [← Int.ediv_neg]; exact ediv_eq_zero_of_lt H1 H2

