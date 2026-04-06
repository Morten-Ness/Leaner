FAIL
import Mathlib

variable {A M G α β γ : Type*}

theorem sumCongrHom_injective {α β : Type*} : Function.Injective (Equiv.Perm.sumCongrHom α β) := by
  intro f g h
  rcases f with ⟨f₁, f₂⟩
  rcases g with ⟨g₁, g₂⟩
  dsimp at h
  congr
  · ext x
    exact Equiv.ext_iff.mp h (Sum.inl x)
  · ext x
    exact Equiv.ext_iff.mp h (Sum.inr x)
