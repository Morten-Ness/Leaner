import Mathlib

theorem natCast_strictMono : StrictMono (· : ℕ → ℤ) := fun _ _ ↦ Int.ofNat_lt.2

