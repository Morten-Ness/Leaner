import Mathlib

variable {R : Type*} [CommRing R]

theorem fst_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (Quaternion.dualNumberEquiv.symm d).imK.fst = d.fst.imK := rfl

