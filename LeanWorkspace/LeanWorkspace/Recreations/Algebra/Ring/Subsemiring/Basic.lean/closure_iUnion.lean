import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_iUnion {ι} (s : ι → Set R) : Subsemiring.closure (⋃ i, s i) = ⨆ i, Subsemiring.closure (s i) := (Subsemiring.gi R).gc.l_iSup

