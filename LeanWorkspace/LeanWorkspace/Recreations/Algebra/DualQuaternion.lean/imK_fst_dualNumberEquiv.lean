import Mathlib

variable {R : Type*} [CommRing R]

theorem imK_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (Quaternion.dualNumberEquiv q).fst.imK = q.imK.fst := rfl

