import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem card_eq_finrank_add_one [Fintype ι] (b : AffineBasis ι k P) :
    Fintype.card ι = Module.finrank k V + 1 := have : FiniteDimensional k V := AffineBasis.finiteDimensional b
  b.ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp b.tot

