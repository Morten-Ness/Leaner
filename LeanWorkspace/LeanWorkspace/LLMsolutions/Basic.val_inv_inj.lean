FAIL
import Mathlib

variable {α : Type u}

variable [Monoid α]

variable (b c : αˣ) {u : αˣ}

theorem val_inv_inj {u₁ u₂ : αˣ} : ((u₁⁻¹ : αˣ) : α) = u₂⁻¹ ↔ (u₁ : α) = u₂ := by
  constructor
  · intro h
    have h' : ((u₁⁻¹ : αˣ) : α) = ((u₂⁻¹ : αˣ) : α) := h
    have hu : (u₁⁻¹ : αˣ) = u₂⁻¹ := Units.ext h'
    exact congrArg (fun x : αˣ => (x⁻¹ : αˣ)) hu |> congrArg (fun x : αˣ => (x : α))
  · intro h
    have hu : u₁ = u₂ := Units.ext h
    exact congrArg (fun x : αˣ => (x⁻¹ : αˣ : αˣ)) hu |> congrArg (fun x : αˣ => (x : α))
