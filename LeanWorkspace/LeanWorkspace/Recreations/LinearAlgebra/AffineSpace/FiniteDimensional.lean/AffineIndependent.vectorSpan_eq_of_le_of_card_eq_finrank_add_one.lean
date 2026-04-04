import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem AffineIndependent.vectorSpan_eq_of_le_of_card_eq_finrank_add_one [Fintype ι] {p : ι → P}
    (hi : AffineIndependent k p) {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (Set.range p) ≤ sm) (hc : Fintype.card ι = finrank k sm + 1) :
    vectorSpan k (Set.range p) = sm := Submodule.eq_of_le_of_finrank_eq hle <| hi.finrank_vectorSpan hc

