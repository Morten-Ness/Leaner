import Mathlib

variable {R : Type*} [CommRing R]

theorem fst_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (Quaternion.dualNumberEquiv.symm d).imJ.fst = d.fst.imJ := rfl

