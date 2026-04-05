import Mathlib

variable {K : Type u} [Field K]

theorem is_eqv : Equivalence (IsBrauerEquivalent (K := K)) where
  IsBrauerEquivalent.refl := IsBrauerEquivalent.refl
  IsBrauerEquivalent.symm := IsBrauerEquivalent.symm
  IsBrauerEquivalent.trans := IsBrauerEquivalent.trans

