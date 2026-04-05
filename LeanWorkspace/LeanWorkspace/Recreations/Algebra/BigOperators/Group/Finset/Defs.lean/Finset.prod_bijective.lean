import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [CommMonoid M]

variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

theorem prod_bijective (e : ι → κ) (he : e.Bijective) (hst : ∀ i, i ∈ s ↔ e i ∈ t)
    (hfg : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ i ∈ t, g i := Finset.prod_equiv (.ofBijective e he) hst hfg

