import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mul_mem_sup {S T : Submonoid M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T := by
  exact Submonoid.mul_mem_sup hx hy
