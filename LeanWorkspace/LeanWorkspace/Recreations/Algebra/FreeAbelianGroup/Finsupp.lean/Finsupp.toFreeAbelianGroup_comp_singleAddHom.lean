import Mathlib

variable {X : Type*}

theorem Finsupp.toFreeAbelianGroup_comp_singleAddHom (x : X) :
    Finsupp.toFreeAbelianGroup.comp (Finsupp.singleAddHom x) =
      (smulAddHom ℤ (FreeAbelianGroup X)).flip (of x) := AddMonoidHom.ext <| toFreeAbelianGroup_single _

