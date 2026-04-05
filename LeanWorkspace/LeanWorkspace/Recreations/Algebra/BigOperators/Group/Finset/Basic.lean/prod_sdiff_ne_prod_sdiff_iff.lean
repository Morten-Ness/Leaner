import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [DecidableEq ι] [CancelCommMonoid M] {s t : Finset ι} {f : ι → M}

theorem prod_sdiff_ne_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i ≠ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≠ ∏ i ∈ t, f i := Finset.prod_sdiff_eq_prod_sdiff_iff.not

