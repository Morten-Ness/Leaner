import Mathlib

theorem coe_of (M : Type u) [Mul M] : (MagmaCat.of M : Type u) = M := rfl

