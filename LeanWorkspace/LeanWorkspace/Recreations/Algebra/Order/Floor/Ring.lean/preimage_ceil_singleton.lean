import Mathlib

variable {F R S : Type*}

variable [Ring R] [LinearOrder R] [FloorRing R] {z : ℤ} {a b : R}

theorem preimage_ceil_singleton (m : ℤ) : (ceil : R → ℤ) ⁻¹' {m} = Ioc ((m : R) - 1) m := ext fun _ => Int.ceil_eq_iff

