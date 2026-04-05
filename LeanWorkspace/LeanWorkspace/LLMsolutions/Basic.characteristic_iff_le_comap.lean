FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem characteristic_iff_le_comap : H.Characteristic ↔ ∀ ϕ : G ≃* G, H ≤ H.comap ϕ.toMonoidHom := by
  rw [Subgroup.characteristic_iff_comap_eq]
  constructor
  · intro h ϕ
    rw [← h ϕ]
    exact le_rfl
  · intro h ϕ
    apply le_antisymm
    · exact h ϕ
    · intro x hx
      have hx' : ϕ x ∈ H := hx
      have hsymm := h ϕ.symm hx'
      simpa using hsymm
