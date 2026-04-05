import Mathlib

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

theorem exists_of_mem_closure_range [Fintype ι] (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι → ℤ, x = ∏ i, f i ^ a i := by
  obtain ⟨a, rfl⟩ := Subgroup.exists_finsupp_of_mem_closure_range f x hx
  exact ⟨a, by simp⟩

