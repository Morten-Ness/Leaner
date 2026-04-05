import Mathlib

variable {α G A S : Type*}

variable [Group G] [AddGroup A] {s : Set G}

variable [Group α] [MulDistribMulAction α G]

theorem conjAct_pointwise_smul_eq_self {H : Subgroup G} {g : G} (hg : g ∈ normalizer H) :
    ConjAct.toConjAct g • H = H := Subgroup.conjAct_pointwise_smul_iff.2 hg

