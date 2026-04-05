import Mathlib

variable {M : Type*} [CommMonoid M] {ι : Type*} (f : ι → M) (x : M)

theorem mem_closure_range_iff :
    x ∈ closure (Set.range f) ↔ ∃ a : ι →₀ ℕ, x = a.prod (f · ^ ·) := by
  refine ⟨Submonoid.exists_finsupp_of_mem_closure_range f x, ?_⟩
  rintro ⟨a, rfl⟩
  exact prod_mem _ fun i hi ↦ pow_mem (subset_closure (Set.mem_range_self i)) _

