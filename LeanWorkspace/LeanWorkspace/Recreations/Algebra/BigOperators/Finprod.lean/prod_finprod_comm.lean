import Mathlib

variable {α β ι G M N : Type*} [CommMonoid M] [CommMonoid N]

variable {f g : α → M} {a b : α} {s t : Set α}

theorem prod_finprod_comm (s : Finset α) (f : α → β → M) (h : ∀ a ∈ s, HasFiniteMulSupport (f a)) :
    (∏ a ∈ s, ∏ᶠ b : β, f a b) = ∏ᶠ b : β, ∏ a ∈ s, f a b := (finprod_prod_comm s (fun b a => f a b) h).symm

