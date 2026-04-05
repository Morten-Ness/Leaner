import Mathlib

variable {α β R n m : Type*}

theorem isDiag_of_subsingleton [Zero α] [Subsingleton n] (A : Matrix n n α) : A.IsDiag := fun i j h => (h <| Subsingleton.elim i j).elim

