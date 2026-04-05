import Mathlib

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

variable [Ring R] [AddCommGroup M]

variable {module_M : Module R M}

variable (p p' : Submodule R M)

variable {r : R} {x y : M}

theorem toAddSubgroup_strictMono : StrictMono (toAddSubgroup : Submodule R M → AddSubgroup M) := fun _ _ => id

