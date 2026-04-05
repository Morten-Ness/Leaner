import Mathlib

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

theorem mem_closure_range_iff_of_fintype [Fintype ι] :
    x ∈ closure (Set.range f) ↔ ∃ a : ι → ℤ, x = ∏ i, f i ^ a i := by
  rw [Finsupp.equivFunOnFinite.symm.exists_congr_left, Subgroup.mem_closure_range_iff]
  simp

