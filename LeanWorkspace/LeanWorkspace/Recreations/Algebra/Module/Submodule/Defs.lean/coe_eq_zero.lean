import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

theorem coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 := (SetLike.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)

