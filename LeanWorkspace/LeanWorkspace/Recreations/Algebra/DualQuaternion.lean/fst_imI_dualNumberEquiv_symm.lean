import Mathlib

variable {R : Type*} [CommRing R]

theorem fst_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (Quaternion.dualNumberEquiv.symm d).imI.fst = d.fst.imI := rfl

