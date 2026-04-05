import Mathlib

variable (A : Type*)

variable {A} [NonUnitalNonAssocRing A] [IsJordan A]

theorem commute_lmul_rmul_sq (a : A) : Commute (L a) (R (a * a)) := AddMonoidHom.ext fun _ => (IsJordan.lmul_comm_rmul_rmul _ _).symm

