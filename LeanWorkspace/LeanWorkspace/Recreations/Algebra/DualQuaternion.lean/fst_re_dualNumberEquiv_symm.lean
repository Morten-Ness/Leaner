import Mathlib

variable {R : Type*} [CommRing R]

theorem fst_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (Quaternion.dualNumberEquiv.symm d).re.fst = d.fst.re := rfl

