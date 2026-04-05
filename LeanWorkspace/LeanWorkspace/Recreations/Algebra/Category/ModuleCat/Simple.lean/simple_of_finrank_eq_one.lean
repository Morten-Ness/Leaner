import Mathlib

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem simple_of_finrank_eq_one {k : Type*} [Field k] [Algebra k R] {V : ModuleCat R}
    (h : finrank k V = 1) : Simple V := (simple_iff_isSimpleModule' V).mpr <| (isSimpleModule_iff ..).mpr <|
    is_simple_module_of_finrank_eq_one h

