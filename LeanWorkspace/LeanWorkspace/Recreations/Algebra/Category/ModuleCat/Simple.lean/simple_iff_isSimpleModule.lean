import Mathlib

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem simple_iff_isSimpleModule : Simple (of R M) ↔ IsSimpleModule R M := by
  rw [simple_iff_subobject_isSimpleOrder, (subobjectModule (of R M)).isSimpleOrder_iff,
    isSimpleModule_iff]

