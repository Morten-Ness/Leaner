import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem range_snd : (snd R S).rangeS = ⊤ := RingHom.rangeS_top_of_surjective (snd R S) <| Prod.snd_surjective

