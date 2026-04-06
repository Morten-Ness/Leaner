import Mathlib

variable {m n : ℤ}

theorem even_iff : Even n ↔ n % 2 = 0 where
  mp := by
    intro h
    simpa [Int.even_iff] using h
  mpr := by
    intro h
    simpa [Int.even_iff] using h
