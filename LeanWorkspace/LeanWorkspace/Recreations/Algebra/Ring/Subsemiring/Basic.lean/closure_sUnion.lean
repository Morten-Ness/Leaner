import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem closure_sUnion (s : Set (Set R)) : Subsemiring.closure (⋃₀ s) = ⨆ t ∈ s, Subsemiring.closure t := (Subsemiring.gi R).gc.l_sSup

