import Mathlib

theorem coe_of (M : Type u) [Monoid M] : (MonCat.of M : Type u) = M := rfl

