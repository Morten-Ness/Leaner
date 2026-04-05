import Mathlib

variable {R : Type*} [CommRing R]

theorem imI_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (Quaternion.dualNumberEquiv q).fst.imI = q.imI.fst := rfl

