import Mathlib

open scoped Pointwise

variable {R G M : Type*}

variable [Semiring R] [IsDomain R] [AddCommMonoid M] [DecidableEq M] [Module R M]
  [IsTorsionFree R M] {s : Finset R} {t : Finset M} {r : R} {m : M}

theorem zero_mem_smul_iff : (0 : M) ∈ s • t ↔ 0 ∈ s ∧ t.Nonempty ∨ 0 ∈ t ∧ s.Nonempty := by
  rw [← mem_coe, coe_smul, Set.zero_mem_smul_iff]; rfl

