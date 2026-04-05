import Mathlib

variable {R : Type*} {M : Type*} [Semiring R]

theorem isLinearMap_sub [AddCommGroup M] [Module R M] :
    IsLinearMap R fun x : M × M => x.1 - x.2 := by
  apply IsLinearMap.mk
  · simp [add_comm, add_assoc, add_left_comm, sub_eq_add_neg]
  · simp [smul_sub]

