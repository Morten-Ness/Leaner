import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_ite {s : Finset ι} {p : ι → Prop} [DecidablePred p] (f g : ι → M) :
    ∏ x ∈ s, (if p x then f x else g x) = (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, g x := by
  simp [Finset.prod_apply_ite _ _ fun x => x]

