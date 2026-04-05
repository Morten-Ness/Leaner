import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable {R' α β : Type*}

variable {S' : Type*} [SetLike S' R'] (s : S)

variable [Semiring R']

theorem closure_le_centralizer_centralizer (s : Set R') :
    Subsemiring.closure s ≤ Subsemiring.centralizer (Subsemiring.centralizer s) := Subsemiring.closure_le.mpr Set.subset_centralizer_centralizer

