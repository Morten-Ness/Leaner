import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem apply_coe_mem_map (f : M →ₙ* N) (S : Subsemigroup M) (x : S) : f x ∈ S.map f := Subsemigroup.mem_map_of_mem f x.prop

