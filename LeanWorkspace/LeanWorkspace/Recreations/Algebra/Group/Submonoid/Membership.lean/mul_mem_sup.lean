import Mathlib

variable {M A B : Type*}

variable [MulOneClass M]

theorem mul_mem_sup {S T : Submonoid M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T := (S ⊔ T).mul_mem (Submonoid.mem_sup_left hx) (Submonoid.mem_sup_right hy)

