import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_apply_ite {s : Finset ι} {p : ι → Prop} [DecidablePred p] (f g : ι → γ)
    (h : γ → M) :
    (∏ x ∈ s, h (if p x then f x else g x)) =
      (∏ x ∈ s with p x, h (f x)) * ∏ x ∈ s with ¬p x, h (g x) := (Finset.prod_apply_dite _ _ _).trans <| congr_arg₂ _ (prod_attach _ (h ∘ f)) (prod_attach _ (h ∘ g))

