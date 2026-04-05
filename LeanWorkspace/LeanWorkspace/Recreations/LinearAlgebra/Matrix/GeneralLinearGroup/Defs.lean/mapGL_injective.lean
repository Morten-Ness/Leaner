import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]
  {S : Type*} [CommRing S] [Algebra R S]

theorem mapGL_injective [FaithfulSMul R S] :
    Function.Injective (Matrix.SpecialLinearGroup.mapGL (R := R) (n := n) S) :=
  fun a b ↦ by simp

