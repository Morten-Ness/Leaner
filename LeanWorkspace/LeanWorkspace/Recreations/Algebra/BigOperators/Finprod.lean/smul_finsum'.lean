import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem smul_finsum' {R M : Type*} [AddCommMonoid M] [DistribSMul R M] (c : R)
    {f : ι → M} (hf : HasFiniteSupport f) : (c • ∑ᶠ i, f i) = ∑ᶠ i, c • f i := (DistribSMul.toAddMonoidHom M c).map_finsum hf

