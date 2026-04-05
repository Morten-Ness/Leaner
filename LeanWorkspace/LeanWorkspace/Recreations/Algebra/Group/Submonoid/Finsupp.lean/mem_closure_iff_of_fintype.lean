import Mathlib

variable {M : Type*} [CommMonoid M] {ι : Type*} (f : ι → M) (x : M)

theorem mem_closure_iff_of_fintype {s : Set M} [Fintype s] :
    x ∈ closure s ↔ ∃ a : s → ℕ, x = ∏ i : s, i.1 ^ a i := by
  conv_lhs => rw [← Subtype.range_coe (s := s)]
  exact Submonoid.mem_closure_range_iff_of_fintype

