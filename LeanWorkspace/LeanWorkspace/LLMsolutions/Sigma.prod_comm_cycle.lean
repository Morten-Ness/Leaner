import Mathlib

variable {ι κ α β γ : Type*}

variable {s s₁ s₂ : Finset α} {a : α} {f g : α → β}

variable [CommMonoid β]

theorem prod_comm_cycle {s : Finset γ} {t : Finset α} {u : Finset κ} {f : γ → α → κ → β} :
    (∏ x ∈ s, ∏ y ∈ t, ∏ z ∈ u, f x y z) = ∏ z ∈ u, ∏ x ∈ s, ∏ y ∈ t, f x y z := by
  calc
    (∏ x ∈ s, ∏ y ∈ t, ∏ z ∈ u, f x y z)
        = ∏ x ∈ s, ∏ z ∈ u, ∏ y ∈ t, f x y z := by
            apply Finset.prod_congr rfl
            intro x hx
            exact Finset.prod_comm
    _ = ∏ z ∈ u, ∏ x ∈ s, ∏ y ∈ t, f x y z := by
          exact Finset.prod_comm
