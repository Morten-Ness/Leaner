import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

variable [IsStrictOrderedRing R]

theorem ceil_eq_on_Ioc' (z : ℤ) : ∀ a ∈ Set.Ioc (z - 1 : R) z, (⌈a⌉ : R) = z := fun a ha =>
  mod_cast Int.ceil_eq_on_Ioc z a ha

