import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem modEq_iff_toIcoMod_ne_toIocMod : a ≡ b [PMOD p] ↔ toIcoMod hp a b ≠ toIocMod hp a b := (AddCommGroup.tfae_modEq hp a b).out 0 2

