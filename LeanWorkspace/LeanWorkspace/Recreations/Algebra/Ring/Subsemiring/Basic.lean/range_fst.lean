import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem range_fst : (fst R S).rangeS = ⊤ := RingHom.rangeS_top_of_surjective (fst R S) <| Prod.fst_surjective

