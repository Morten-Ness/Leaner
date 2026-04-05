import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_extend_by_one [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    ∏ i ∈ s, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i := (Finset.prod_congr rfl) fun _i hi => if_pos hi

