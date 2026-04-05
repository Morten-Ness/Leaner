import Mathlib

open scoped Pointwise

variable {R G M : Type*}

variable [Semiring R] [IsDomain R] [AddCommMonoid M] [DecidableEq M] [Module R M]
  [IsTorsionFree R M] {s : Finset R} {t : Finset M} {r : R} {m : M}

theorem zero_mem_smul_finset_iff (hr : r ≠ 0) : 0 ∈ r • t ↔ 0 ∈ t := by
  rw [← mem_coe, coe_smul_finset, Set.zero_mem_smul_set_iff hr, mem_coe]

