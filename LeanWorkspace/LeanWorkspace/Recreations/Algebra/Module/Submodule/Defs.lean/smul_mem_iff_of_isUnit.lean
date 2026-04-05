import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

theorem smul_mem_iff_of_isUnit (hr : IsUnit r) :
    r • x ∈ p ↔ x ∈ p := let _ : Invertible r := hr.invertible
  Submodule.smul_mem_iff'' p

