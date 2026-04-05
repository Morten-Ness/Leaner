import Mathlib

variable {R : Type*} [CommRing R]

theorem snd_imK_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (Quaternion.dualNumberEquiv.symm d).imK.snd = d.snd.imK := rfl

