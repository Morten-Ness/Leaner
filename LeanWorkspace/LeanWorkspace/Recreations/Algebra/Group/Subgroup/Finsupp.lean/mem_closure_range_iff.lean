import Mathlib

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

theorem mem_closure_range_iff :
    x ∈ closure (Set.range f) ↔ ∃ a : ι →₀ ℤ, x = a.prod (f · ^ ·) := by
  refine ⟨Subgroup.exists_finsupp_of_mem_closure_range f x, ?_⟩
  rintro ⟨a, rfl⟩
  exact Submonoid.prod_mem _ fun i hi ↦ zpow_mem (subset_closure (Set.mem_range_self i)) _

