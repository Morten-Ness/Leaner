import Mathlib

variable {ι : Sort*} {M : Type*}

variable [Mul M]

theorem mul_mem_sup {S T : Subsemigroup M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T := mul_mem (Subsemigroup.mem_sup_left hx) (Subsemigroup.mem_sup_right hy)

