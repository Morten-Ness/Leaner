import Mathlib

variable {G M N A α : Type*}

variable (G α) [AddGroup G] [AddAction G α]

theorem AddAction.toPerm_zero :
    (AddAction.toPerm (0 : G)) = (1 : Equiv.Perm α) := by
  aesop

