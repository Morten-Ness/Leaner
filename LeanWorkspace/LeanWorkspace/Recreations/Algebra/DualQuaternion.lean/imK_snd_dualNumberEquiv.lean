import Mathlib

variable {R : Type*} [CommRing R]

theorem imK_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (Quaternion.dualNumberEquiv q).snd.imK = q.imK.snd := rfl

