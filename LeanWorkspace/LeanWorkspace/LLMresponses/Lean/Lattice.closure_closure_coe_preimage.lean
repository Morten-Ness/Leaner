FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_closure_coe_preimage {k : Set G} : Subgroup.closure (((↑) : Subgroup.closure k → G) ⁻¹' k) = ⊤ := by
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    change x ∈ Subgroup.closure (((↑) : Subgroup.closure k → G) ⁻¹' k)
    refine Subgroup.closure_induction x.property ?h ?one ?mul ?inv
    · intro y hy
      exact Subgroup.subset_closure hy
    · exact Subgroup.one_mem _
    · intro a b ha hb
      exact Subgroup.mul_mem _ ha hb
    · intro a ha
      exact Subgroup.inv_mem _ ha
