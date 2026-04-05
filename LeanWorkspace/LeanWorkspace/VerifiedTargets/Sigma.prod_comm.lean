import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_comm {s : Finset γ} {t : Finset α} {f : γ → α → β} :
    (∏ x ∈ s, ∏ y ∈ t, f x y) = ∏ y ∈ t, ∏ x ∈ s, f x y := Finset.prod_comm' fun _ _ => Iff.rfl

