import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_closure_coe_preimage {k : Set G} : Subgroup.closure (((↑) : Subgroup.closure k → G) ⁻¹' k) = ⊤ := eq_top_iff.2 fun x _ ↦ Subtype.recOn x fun _ hx' ↦
    Subgroup.closure_induction (fun _ h ↦ Subgroup.subset_closure h) (one_mem _) (fun _ _ _ _ ↦ mul_mem)
      (fun _ _ ↦ inv_mem) hx'

