import Mathlib

variable {R : Type*} [CommRing R]

theorem snd_imJ_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (Quaternion.dualNumberEquiv.symm d).imJ.snd = d.snd.imJ := rfl

