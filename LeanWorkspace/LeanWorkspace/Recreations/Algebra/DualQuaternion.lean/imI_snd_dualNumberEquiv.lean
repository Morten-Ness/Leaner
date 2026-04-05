import Mathlib

variable {R : Type*} [CommRing R]

theorem imI_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (Quaternion.dualNumberEquiv q).snd.imI = q.imI.snd := rfl

