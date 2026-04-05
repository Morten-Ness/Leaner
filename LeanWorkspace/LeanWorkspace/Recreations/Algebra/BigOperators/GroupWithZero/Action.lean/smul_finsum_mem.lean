import Mathlib

variable {M N γ : Type*}

variable [AddCommMonoid N] [DistribSMul M N] {r : M}

theorem smul_finsum_mem {f : γ → N} {s : Set γ} (hs : s.Finite) :
    r • ∑ᶠ x ∈ s, f x = ∑ᶠ x ∈ s, r • f x := (DistribSMul.toAddMonoidHom N r).map_finsum_mem f hs

