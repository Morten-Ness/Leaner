import Mathlib

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

theorem HasTrivialRadical.eq_bot_of_isSolvable [HasTrivialRadical R L]
    (I : LieIdeal R L) [hI : IsSolvable I] : I = ⊥ := sSup_eq_bot.mp radical_eq_bot _ hI

