import Mathlib

variable {R : Type*} [CommRing R]

theorem re_snd_dualNumberEquiv (q : Quaternion (DualNumber R)) :
    (Quaternion.dualNumberEquiv q).snd.re = q.re.snd := rfl

