import Mathlib

variable {G : Type*} {P : Type*} [AddGroup G] [T : AddTorsor G P]

theorem vsub_ne_zero {p q : P} : p -ᵥ q ≠ (0 : G) ↔ p ≠ q := not_congr vsub_eq_zero_iff_eq

