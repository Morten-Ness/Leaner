import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_finset_product (r : Finset (γ × α)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ × α → β} :
    ∏ p ∈ r, f p = ∏ c ∈ s, ∏ a ∈ t c, f (c, a) := by
  refine Eq.trans ?_ (Finset.prod_sigma s t fun p => f (p.1, p.2))
  apply prod_equiv (Equiv.sigmaEquivProd _ _).symm <;> simp [h]

