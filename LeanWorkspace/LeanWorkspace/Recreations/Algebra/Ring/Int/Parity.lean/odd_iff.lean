import Mathlib

variable {m n : ℤ}

theorem odd_iff : Odd n ↔ n % 2 = 1 where
  mp := fun ⟨m, hm⟩ ↦ by grind
  mpr h := ⟨n / 2, by grind⟩

