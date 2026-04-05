import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_cond_nonneg {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {p : α → Prop} {f : α → R}
    (hf : ∀ x, p x → 0 ≤ f x) : 0 ≤ ∏ᶠ (x) (_ : p x), f x := finprod_nonneg fun x => finprod_nonneg <| hf x

