import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite_of_false {p : ι → Prop} [DecidablePred p] (h : ∀ x ∈ s, ¬p x) (f g : ι → M) :
    ∏ x ∈ s, (if p x then f x else g x) = ∏ x ∈ s, g x := (Finset.prod_dite_of_false h _ _).trans (prod_attach _ _)

