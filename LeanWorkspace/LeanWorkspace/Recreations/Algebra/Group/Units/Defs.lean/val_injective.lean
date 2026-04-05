import Mathlib

variable {α : Type u}

variable [Monoid α]

theorem val_injective : Function.Injective (val : αˣ → α)
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    simp only at e; subst v'; congr
    simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁
