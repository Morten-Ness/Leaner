import Mathlib

variable (A : Type*)

variable {A} [NonUnitalNonAssocRing A] [IsJordan A]

theorem commute_rmul_rmul_sq (a : A) : Commute (R a) (R (a * a)) := AddMonoidHom.ext fun _ => (IsJordan.rmul_comm_rmul_rmul _ _).symm

