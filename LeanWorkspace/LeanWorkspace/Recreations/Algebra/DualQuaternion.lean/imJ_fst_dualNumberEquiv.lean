import Mathlib

variable {R : Type*} [CommRing R]

theorem imJ_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (Quaternion.dualNumberEquiv q).fst.imJ = q.imJ.fst := rfl

