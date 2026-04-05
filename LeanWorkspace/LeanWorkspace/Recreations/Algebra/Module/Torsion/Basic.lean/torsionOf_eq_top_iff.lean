import Mathlib

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

theorem torsionOf_eq_top_iff (m : M) : Ideal.torsionOf R M m = ⊤ ↔ m = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  rw [← one_smul R m, ← Ideal.mem_torsionOf_iff m (1 : R), h]
  exact Submodule.mem_top

