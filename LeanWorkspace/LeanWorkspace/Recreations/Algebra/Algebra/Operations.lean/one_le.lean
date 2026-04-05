import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A]

theorem one_le {P : Submodule R A} : (1 : Submodule R A) ≤ P ↔ (1 : A) ∈ P := by
  simp [Submodule.one_eq_span]

