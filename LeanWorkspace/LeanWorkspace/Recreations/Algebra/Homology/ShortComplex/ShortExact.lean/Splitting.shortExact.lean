import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C]

theorem Splitting.shortExact {S : CategoryTheory.ShortComplex C} [HasZeroObject C] (s : S.Splitting) :
    S.ShortExact where
  exact := s.exact
  mono_f := s.mono_f
  epi_g := s.epi_g

