import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_subtype_eq_finprod_cond (p : α → Prop) :
    ∏ᶠ j : Subtype p, f j = ∏ᶠ (i) (_ : p i), f i := finprod_set_coe_eq_finprod_mem { i | p i }

