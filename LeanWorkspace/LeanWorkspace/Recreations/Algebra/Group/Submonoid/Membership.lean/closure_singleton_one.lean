import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem closure_singleton_one : closure ({1} : Set M) = ⊥ := by
  simp [eq_bot_iff_forall, Submonoid.mem_closure_singleton]

