import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem mem_map_iff_mem {f : M →ₙ* N} (hf : Function.Injective f) {S : Subsemigroup M} {x : M} :
    f x ∈ S.map f ↔ x ∈ S := hf.mem_set_image

