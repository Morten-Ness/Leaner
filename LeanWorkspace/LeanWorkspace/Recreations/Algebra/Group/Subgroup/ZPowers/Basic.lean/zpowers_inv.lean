import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

variable {s : Set G} {g : G}

theorem zpowers_inv : Subgroup.zpowers g⁻¹ = Subgroup.zpowers g := eq_of_forall_ge_iff fun _ ↦ by simp only [Subgroup.zpowers_le, inv_mem_iff]

