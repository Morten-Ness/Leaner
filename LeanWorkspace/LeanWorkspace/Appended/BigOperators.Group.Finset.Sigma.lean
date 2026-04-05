import Mathlib

section

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_comm {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x ∈ s, ∏ y ∈ t, f x y) = ∏ y ∈ t, ∏ x ∈ s, f x y := Finset.prod_comm' fun _ _ => Iff.rfl

end

section

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_comm_cycle {s : Finset γ} {t : Finset α} {u : Finset κ} {f : γ → α → κ → β} :
    (∏ x ∈ s, ∏ y ∈ t, ∏ z ∈ u, f x y z) = ∏ z ∈ u, ∏ x ∈ s, ∏ y ∈ t, f x y z := by
  simp_rw [Finset.prod_comm (s := t), Finset.prod_comm (s := s)]

end

section

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_finset_product_right' (r : Finset (α × γ)) (s : Finset γ) (t : γ → Finset α)
    (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α → γ → β} :
    ∏ p ∈ r, f p.1 p.2 = ∏ c ∈ s, ∏ a ∈ t c, f a c := Finset.prod_finset_product_right r s t h

end

section

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_sigma' {σ : α → Type*} (s : Finset α) (t : ∀ a, Finset (σ a)) (f : ∀ a, σ a → β) :
    (∏ a ∈ s, ∏ s ∈ t a, f a s) = ∏ x ∈ s.sigma t, f x.1 x.2 := Eq.symm <| Finset.prod_sigma s t fun x => f x.1 x.2

end
