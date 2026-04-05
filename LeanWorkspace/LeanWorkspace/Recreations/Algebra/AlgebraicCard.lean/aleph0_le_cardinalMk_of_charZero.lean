import Mathlib

theorem aleph0_le_cardinalMk_of_charZero (R A : Type*) [CommRing R] [Ring A]
    [Algebra R A] [CharZero A] : ℵ₀ ≤ #{ x : A // IsAlgebraic R x } := infinite_iff.1 (Set.infinite_coe_iff.2 <| Algebraic.infinite_of_charZero R A)

