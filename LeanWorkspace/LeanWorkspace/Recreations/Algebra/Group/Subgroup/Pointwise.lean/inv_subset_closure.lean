import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

theorem inv_subset_closure (S : Set G) : S⁻¹ ⊆ closure S := fun s hs => by
  rw [SetLike.mem_coe, ← Subgroup.inv_mem_iff]
  exact subset_closure (mem_inv.mp hs)

