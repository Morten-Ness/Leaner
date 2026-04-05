import Mathlib

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

theorem Finset.smul_prod' {r : M} {f : γ → N} {s : Finset γ} :
    (r • ∏ x ∈ s, f x) = ∏ x ∈ s, r • f x := map_prod (MulDistribMulAction.toMonoidHom N r) f s

