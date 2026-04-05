import Mathlib

variable {ι α β M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [One M] [One N]

variable [FunLike F M N]

theorem Subsingleton.of_oneHomClass [Subsingleton M] [OneHomClass F M N] :
    Subsingleton F where
  allEq f g := DFunLike.ext _ _ fun x ↦ by simp [Subsingleton.elim x 1]

