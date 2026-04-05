import Mathlib

variable {M A B : Type*}

variable [AddMonoid A]

theorem closure_singleton_zero : closure ({0} : Set A) = ⊥ := by
  simp [eq_bot_iff_forall, AddSubmonoid.mem_closure_singleton, nsmul_zero]

