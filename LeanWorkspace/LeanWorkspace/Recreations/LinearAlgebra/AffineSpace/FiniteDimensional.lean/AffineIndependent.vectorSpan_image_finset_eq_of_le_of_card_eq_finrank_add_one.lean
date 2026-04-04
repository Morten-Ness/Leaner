import Mathlib

variable (k : Type*) {V : Type*} {P : Type*}

variable {ι : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable {k}

variable (k)

theorem AffineIndependent.vectorSpan_image_finset_eq_of_le_of_card_eq_finrank_add_one
    [DecidableEq P] {p : ι → P}
    (hi : AffineIndependent k p) {s : Finset ι} {sm : Submodule k V} [FiniteDimensional k sm]
    (hle : vectorSpan k (s.image p : Set P) ≤ sm) (hc : #s = finrank k sm + 1) :
    vectorSpan k (s.image p : Set P) = sm := Submodule.eq_of_le_of_finrank_eq hle <| hi.finrank_vectorSpan_image_finset hc

