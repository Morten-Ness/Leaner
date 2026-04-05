import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_hom₂ [CommMonoid O] (s : Multiset ι) (f : M → N → O)
    (hf : ∀ a b c d, f (a * b) (c * d) = f a c * f b d) (hf' : f 1 1 = 1) (f₁ : ι → M)
    (f₂ : ι → N) : (s.map fun i => f (f₁ i) (f₂ i)).prod = f (s.map f₁).prod (s.map f₂).prod := Quotient.inductionOn s fun l => by
    simp only [l.prod_hom₂ f hf hf', quot_mk_to_coe, map_coe, prod_coe]

