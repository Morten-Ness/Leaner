import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Ring R] [AddCommGroup M]

variable {module_M : Module R M}

variable (p p' : Submodule R M)

variable {r : R} {x y : M}

theorem add_mem_iff_right : x ∈ p → (x + y ∈ p ↔ y ∈ p) := add_mem_cancel_left

