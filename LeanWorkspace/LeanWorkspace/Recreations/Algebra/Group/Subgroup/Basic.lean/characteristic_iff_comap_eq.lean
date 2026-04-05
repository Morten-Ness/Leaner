import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem characteristic_iff_comap_eq : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H := ⟨Characteristic.fixed, Characteristic.mk⟩

