import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem exists_inv_mem_iff_exists_mem (K : Subgroup G) {P : G → Prop} :
    (∃ x : G, x ∈ K ∧ P x⁻¹) ↔ ∃ x ∈ K, P x := exists_inv_mem_iff_exists_mem

