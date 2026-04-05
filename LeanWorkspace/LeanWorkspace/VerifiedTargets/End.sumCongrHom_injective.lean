import Mathlib

variable {A M G α β γ : Type*}

theorem sumCongrHom_injective {α β : Type*} : Function.Injective (Equiv.Perm.sumCongrHom α β) := by
  rintro ⟨⟩ ⟨⟩ h
  rw [Prod.mk_inj]
  constructor <;> ext i
  · simpa using Equiv.congr_fun h (Sum.inl i)
  · simpa using Equiv.congr_fun h (Sum.inr i)

