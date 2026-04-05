import Mathlib

variable {R : Type*} [CommRing R]

theorem snd_imI_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (Quaternion.dualNumberEquiv.symm d).imI.snd = d.snd.imI := rfl

