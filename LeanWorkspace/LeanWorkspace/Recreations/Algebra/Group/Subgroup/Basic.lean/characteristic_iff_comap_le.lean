import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem characteristic_iff_comap_le : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom ≤ H := Subgroup.characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => le_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (h ϕ) fun g hg => h ϕ.symm ((congr_arg (· ∈ H) (ϕ.symm_apply_apply g)).mpr hg)⟩

