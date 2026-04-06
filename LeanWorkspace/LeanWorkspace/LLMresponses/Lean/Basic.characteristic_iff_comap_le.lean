FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem characteristic_iff_comap_le : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom ≤ H := by
  constructor
  · intro h ϕ
    rw [Subgroup.characteristic_iff_comap_eq] at h
    simpa [h ϕ] using (le_rfl : H ≤ H)
  · intro h
    rw [Subgroup.characteristic_iff_comap_eq]
    intro ϕ
    apply le_antisymm
    · exact h ϕ
    · intro x hx
      have hx' : ϕ x ∈ H := by
        exact h ϕ.symm (show x ∈ H.comap ϕ.symm.toMonoidHom from hx)
      simpa using hx'
