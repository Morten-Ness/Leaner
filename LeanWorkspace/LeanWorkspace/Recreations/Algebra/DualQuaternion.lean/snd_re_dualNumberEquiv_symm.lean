import Mathlib

variable {R : Type*} [CommRing R]

theorem snd_re_dualNumberEquiv_symm (d : DualNumber (Quaternion R)) :
    (Quaternion.dualNumberEquiv.symm d).re.snd = d.snd.re := rfl

