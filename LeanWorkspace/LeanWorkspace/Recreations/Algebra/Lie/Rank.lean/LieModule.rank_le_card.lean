import Mathlib

variable {R A L M ι ιₘ : Type*}

variable [CommRing R]

variable [CommRing A] [Algebra R A]

variable [LieRing L] [LieAlgebra R L] [Module.Finite R L] [Module.Free R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [Module.Finite R M] [Module.Free R M]

variable [Fintype ι]

variable [Fintype ιₘ]

variable (b : Basis ι R L) (bₘ : Basis ιₘ R M) (x : L)

include bₘ in
theorem rank_le_card [Nontrivial R] : LieModule.rank R L M ≤ Fintype.card ιₘ := nilRank_le_card _ bₘ

