import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

theorem characteristic_iff_map_eq : H.Characteristic ↔ ∀ ϕ : G ≃* G, H.map ϕ.toMonoidHom = H := by
  simp_rw [map_equiv_eq_comap_symm']
  exact Subgroup.characteristic_iff_comap_eq.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

