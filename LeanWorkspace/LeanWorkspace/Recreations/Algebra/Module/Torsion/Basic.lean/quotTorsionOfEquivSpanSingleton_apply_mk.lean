import Mathlib

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

theorem quotTorsionOfEquivSpanSingleton_apply_mk (x : M) (a : R) :
    Ideal.quotTorsionOfEquivSpanSingleton R M x (Submodule.Quotient.mk a) =
      a • ⟨x, Submodule.mem_span_singleton_self x⟩ := rfl

