import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finsum_smul' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {f : ι → R}
    (hf : HasFiniteSupport f) (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x := ((smulAddHom R M).flip x).map_finsum hf

