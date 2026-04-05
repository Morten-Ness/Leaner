import Mathlib

variable {R : Type*} [CommRing R]

theorem re_fst_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (Quaternion.dualNumberEquiv q).fst.re = q.re.fst := rfl

