import Mathlib

variable (A : Type*)

variable {A} [NonUnitalNonAssocRing A] [IsJordan A]

theorem commute_lmul_sq_rmul (a : A) : Commute (L (a * a)) (R a) := AddMonoidHom.ext fun _ => IsJordan.lmul_lmul_comm_rmul _ _

