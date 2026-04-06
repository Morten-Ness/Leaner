import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {s : Set G} {g : G}

theorem zpowers_inv : Subgroup.zpowers g⁻¹ = Subgroup.zpowers g := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    simp
  · rintro ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    simp
