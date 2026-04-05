import Mathlib

section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem simple_iff_isSimpleModule : Simple (of R M) ↔ IsSimpleModule R M := by
  rw [simple_iff_subobject_isSimpleOrder, (subobjectModule (of R M)).isSimpleOrder_iff,
    isSimpleModule_iff]

end

section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem simple_of_finrank_eq_one {k : Type*} [Field k] [Algebra k R] {V : ModuleCat R}
    (h : finrank k V = 1) : Simple V := (simple_iff_isSimpleModule' V).mpr <| (isSimpleModule_iff ..).mpr <|
    is_simple_module_of_finrank_eq_one h

end
