import Mathlib

variable {M N γ : Type*}

variable [AddCommMonoid N] [DistribSMul M N] {r : M}

theorem Finset.smul_sum {f : γ → N} {s : Finset γ} :
    (r • ∑ x ∈ s, f x) = ∑ x ∈ s, r • f x := map_sum (DistribSMul.toAddMonoidHom N r) f s

