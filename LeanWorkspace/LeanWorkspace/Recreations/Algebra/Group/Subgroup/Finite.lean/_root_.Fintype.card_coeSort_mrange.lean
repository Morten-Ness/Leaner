import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem _root_.Fintype.card_coeSort_mrange {M N : Type*} [Monoid M] [Monoid N] [Fintype M]
    [DecidableEq N] {f : M →* N} (hf : Function.Injective f) :
    Fintype.card (mrange f) = Fintype.card M := Set.card_range_of_injective hf

