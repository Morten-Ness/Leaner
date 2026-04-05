import Mathlib

variable (A : Type*)

variable {A} [NonUnitalNonAssocRing A] [IsJordan A]

theorem commute_lmul_lmul_sq (a : A) : Commute (L a) (L (a * a)) := AddMonoidHom.ext fun _ => (IsJordan.lmul_lmul_comm_lmul _ _).symm

