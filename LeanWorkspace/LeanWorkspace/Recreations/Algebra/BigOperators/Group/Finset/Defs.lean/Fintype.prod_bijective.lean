import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

variable [Fintype ι] [Fintype κ]

variable [CommMonoid M]

theorem prod_bijective (e : ι → κ) (he : e.Bijective) (f : ι → M) (g : κ → M)
    (h : ∀ x, f x = g (e x)) : ∏ x, f x = ∏ x, g x := Finset.prod_equiv (.ofBijective e he) (by simp) (by simp [h])

