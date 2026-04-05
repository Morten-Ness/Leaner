import Mathlib

theorem two_le_iff_pos_of_even {m : ℤ} (even : Even m) : 2 ≤ m ↔ 0 < m := le_iff_pos_of_dvd (by decide) even.two_dvd

