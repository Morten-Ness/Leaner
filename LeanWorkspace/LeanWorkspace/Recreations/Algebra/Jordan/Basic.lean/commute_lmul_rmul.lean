import Mathlib

variable (A : Type*)

variable {A} [NonUnitalNonAssocRing A] [IsJordan A]

theorem commute_lmul_rmul (a : A) : Commute (L a) (R a) := AddMonoidHom.ext fun _ => (IsJordan.lmul_comm_rmul _ _).symm

