import Mathlib

theorem infinite_of_charZero (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
    [CharZero A] : { x : A | IsAlgebraic R x }.Infinite := by
  letI := MulActionWithZero.nontrivial R A
  exact infinite_of_injective_forall_mem Nat.cast_injective isAlgebraic_nat

