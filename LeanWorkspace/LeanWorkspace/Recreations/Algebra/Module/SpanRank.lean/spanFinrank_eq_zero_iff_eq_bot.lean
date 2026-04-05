import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanFinrank_eq_zero_iff_eq_bot {p : Submodule R M} (h : p.FG) :
    p.spanFinrank = 0 ↔ p = ⊥ := by
  refine ⟨fun heq ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← Submodule.FG.generators_ncard h, Set.ncard_eq_zero h.finite_generators] at heq
  rw [← Submodule.span_generators p, heq, span_empty]

