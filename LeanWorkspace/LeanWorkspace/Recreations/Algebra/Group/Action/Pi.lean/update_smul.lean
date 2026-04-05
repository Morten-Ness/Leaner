import Mathlib

variable {ι M N : Type*} {α β γ : ι → Type*} (i : ι)

theorem update_smul [∀ i, SMul M (α i)] [DecidableEq ι] (c : M) (f₁ : ∀ i, α i)
    (i : ι) (x₁ : α i) : Function.update (c • f₁) i (c • x₁) = c • Function.update f₁ i x₁ := funext fun j => (apply_update (β := α) (fun _ ↦ (c • ·)) f₁ i x₁ j).symm

