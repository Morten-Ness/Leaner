import Mathlib

variable {G M N A α : Type*}

variable (G α) [Group G] [MulAction G α]

theorem MulAction.toPerm_one :
    (MulAction.toPerm (1 : G)) = (1 : Equiv.Perm α) := by
  aesop

