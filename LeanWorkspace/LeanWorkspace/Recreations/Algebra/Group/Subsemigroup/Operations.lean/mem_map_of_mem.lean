import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem mem_map_of_mem (f : M →ₙ* N) {S : Subsemigroup M} {x : M} (hx : x ∈ S) : f x ∈ S.map f := mem_image_of_mem f hx

