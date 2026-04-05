import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem characteristic_iff_le_comap : H.Characteristic ↔ ∀ ϕ : G ≃* G, H ≤ H.comap ϕ.toMonoidHom := Subgroup.characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => ge_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (fun g hg => (congr_arg (· ∈ H) (ϕ.symm_apply_apply g)).mp (h ϕ.symm hg)) (h ϕ)⟩

