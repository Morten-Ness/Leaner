import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_apply_ite_of_false {p : ι → Prop} [DecidablePred p] (f g : ι → γ) (k : γ → M)
    (h : ∀ x ∈ s, ¬p x) : (∏ x ∈ s, k (if p x then f x else g x)) = ∏ x ∈ s, k (g x) := by
  refine Finset.prod_congr rfl ?_
  intro x hx
  simp [h x hx]
