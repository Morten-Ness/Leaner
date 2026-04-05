import Mathlib

variable {R : Type*} [CommRing R]

theorem imJ_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (Quaternion.dualNumberEquiv q).snd.imJ = q.imJ.snd := rfl

