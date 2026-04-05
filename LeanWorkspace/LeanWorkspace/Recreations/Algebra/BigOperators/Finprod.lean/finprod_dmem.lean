import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem finprod_dmem {s : Set α} [DecidablePred (· ∈ s)] (f : ∀ a : α, a ∈ s → M) :
    (∏ᶠ (a : α) (h : a ∈ s), f a h) = ∏ᶠ (a : α) (_ : a ∈ s), if h' : a ∈ s then f a h' else 1 := finprod_congr fun _ => finprod_congr fun ha => (dif_pos ha).symm

