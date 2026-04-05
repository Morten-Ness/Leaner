import Mathlib

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

theorem mem_closure_iff_of_fintype {s : Set M} [Fintype s] :
    x ∈ closure s ↔ ∃ a : s → ℤ, x = ∏ i : s, i.1 ^ a i := by
  conv_lhs => rw [← Subtype.range_coe (s := s)]
  exact Subgroup.mem_closure_range_iff_of_fintype

