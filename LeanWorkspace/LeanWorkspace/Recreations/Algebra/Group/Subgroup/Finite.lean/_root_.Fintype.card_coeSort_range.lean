import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem _root_.Fintype.card_coeSort_range [Fintype G] [DecidableEq N] {f : G →* N}
    (hf : Function.Injective f) :
    Fintype.card (range f) = Fintype.card G := Set.card_range_of_injective hf

