import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

theorem AffineIndependent.vectorSpan_eq_top_of_card_eq_finrank_add_one [FiniteDimensional k V]
    [Fintype ι] {p : ι → P} (hi : AffineIndependent k p) (hc : Fintype.card ι = finrank k V + 1) :
    vectorSpan k (Set.range p) = ⊤ := Submodule.eq_top_of_finrank_eq <| hi.finrank_vectorSpan hc

