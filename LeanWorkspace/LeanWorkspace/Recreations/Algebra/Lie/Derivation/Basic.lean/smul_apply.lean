import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

variable {S T : Type*}

variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulBracketCommClass S L M]

variable [Monoid T] [DistribMulAction T M] [SMulCommClass R T M] [SMulBracketCommClass T L M]

theorem smul_apply (r : S) (D : LieDerivation R L M) : (r • D) a = r • D a := rfl

