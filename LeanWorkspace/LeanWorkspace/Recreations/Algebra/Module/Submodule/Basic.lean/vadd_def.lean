import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Semiring R] [AddCommMonoid M]

variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

variable {α β : Type*}

theorem vadd_def [VAdd M α] (g : p) (m : α) : g +ᵥ m = (g : M) +ᵥ m := rfl

