import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable (A B : SpecialLinearGroup n R)

theorem coe_inv : ↑ₘ(A⁻¹) = adjugate A := rfl

