import Mathlib

variable {ι κ M N G α : Type*}

theorem prod_mk [CommMonoid M] (s : Multiset ι) (hs : s.Nodup) (f : ι → M) :
    (⟨s, hs⟩ : Finset ι).prod f = (s.map f).prod := rfl

