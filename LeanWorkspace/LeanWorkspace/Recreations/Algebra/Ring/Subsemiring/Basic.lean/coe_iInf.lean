import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem coe_iInf {ι : Sort*} {S : ι → Subsemiring R} : (↑(⨅ i, S i) : Set R) = ⋂ i, S i := by
  simp only [iInf, Subsemiring.coe_sInf, Set.biInter_range]

