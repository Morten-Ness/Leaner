import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

theorem mk_eq_zero {x} (h : x ∈ p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 := Subtype.ext_iff

