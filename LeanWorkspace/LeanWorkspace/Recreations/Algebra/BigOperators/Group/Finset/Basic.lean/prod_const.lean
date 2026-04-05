import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_const (b : M) : ∏ _x ∈ s, b = b ^ #s := (congr_arg _ <| s.val.map_const b).trans <| Multiset.prod_replicate #s b

