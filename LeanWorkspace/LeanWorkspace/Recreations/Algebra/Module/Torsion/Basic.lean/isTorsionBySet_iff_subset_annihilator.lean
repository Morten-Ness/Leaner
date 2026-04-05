import Mathlib

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

theorem isTorsionBySet_iff_subset_annihilator {s : Set R} :
    IsTorsionBySet R M s ↔ s ⊆ annihilator R M := by
  simp_rw [IsTorsionBySet, Set.subset_def, SetLike.mem_coe, mem_annihilator]
  rw [forall_comm, SetCoe.forall]

