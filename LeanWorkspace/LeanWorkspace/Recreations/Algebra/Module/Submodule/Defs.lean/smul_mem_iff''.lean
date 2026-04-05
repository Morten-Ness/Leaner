import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

theorem smul_mem_iff'' [Invertible r] :
    r • x ∈ p ↔ x ∈ p := by
  refine ⟨fun h ↦ ?_, Submodule.smul_mem p r⟩
  rw [← invOf_smul_smul r x]
  exact Submodule.smul_mem p _ h

