FAIL
import Mathlib

variable {R : Type u} [Semiring R] {A : Type v} [Semiring A] [Module R A] [SMulCommClass R A A]
  [IsScalarTower R A A]

theorem one_eq_span : (1 : Submodule R A) = R ∙ 1 := by
  ext x
  constructor
  · intro hx
    rw [Submodule.mem_span_singleton]
    refine ⟨x, ?_⟩
    simpa using hx
  · intro hx
    rw [Submodule.mem_span_singleton] at hx
    rcases hx with ⟨a, rfl⟩
    exact Submodule.one_smul_mem (1 : Submodule R A) a
