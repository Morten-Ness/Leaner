import Mathlib

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} :
    x ∈ K.map (f : M →ₙ* N) ↔ f.symm x ∈ K := @Set.mem_image_equiv _ _ (K : Set M) f.toEquiv x

