import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_finset_product_right (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α × γ → β} :
    ∏ p ∈ r, f p = ∏ c ∈ s, ∏ a ∈ t c, f (a, c) := by
  refine Eq.trans ?_ (Finset.prod_sigma s t fun p => f (p.2, p.1))
  apply prod_equiv ((Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm) <;> simp [h]

