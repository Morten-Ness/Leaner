import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_dite_of_true {p : ι → Prop} [DecidablePred p] (h : ∀ i ∈ s, p i) (f : ∀ i, p i → M)
    (g : ∀ i, ¬ p i → M) :
    ∏ i ∈ s, (if hi : p i then f i hi else g i hi) = ∏ i : s, f i.1 (h _ i.2) := by
  refine prod_bij' (fun x hx => ⟨x, hx⟩) (fun x _ ↦ x) ?_ ?_ ?_ ?_ ?_ <;> grind

