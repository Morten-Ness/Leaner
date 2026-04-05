import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem smul_opposite_mul {H : Subgroup G} (x g : G) (h : H.op) :
    h • (g * x) = g * h • x := mul_assoc _ _ _

