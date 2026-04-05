import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem prod_int_mod (s : Finset ι) (n : ℤ) (f : ι → ℤ) :
    (∏ i ∈ s, f i) % n = (∏ i ∈ s, f i % n) % n := (Multiset.prod_int_mod _ _).trans <| by rw [Finset.prod, Multiset.map_map]; rfl

