import Mathlib

variable {ι ι' R R₂ M M' : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b : Basis ι R M)

theorem mem_submodule_iff {P : Submodule R M} (b : Module.Basis ι R P) {x : M} :
    x ∈ P ↔ ∃ c : ι →₀ R, x = Finsupp.sum c fun i x => x • (b i : M) := by
  conv_lhs =>
    rw [← P.range_subtype, ← Submodule.map_top, ← b.span_eq, Submodule.map_span, ← Set.range_comp,
        ← Finsupp.range_linearCombination]
  simp [@eq_comm _ x, Function.comp, Finsupp.linearCombination_apply]

