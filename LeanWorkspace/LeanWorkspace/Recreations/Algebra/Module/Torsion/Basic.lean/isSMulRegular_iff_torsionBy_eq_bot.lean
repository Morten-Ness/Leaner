import Mathlib

theorem isSMulRegular_iff_torsionBy_eq_bot {R} (M : Type*)
    [CommRing R] [AddCommGroup M] [Module R M] (r : R) :
    IsSMulRegular M r ↔ Submodule.torsionBy R M r = ⊥ := (DistribSMul.toLinearMap R M r).ker_eq_bot.symm

