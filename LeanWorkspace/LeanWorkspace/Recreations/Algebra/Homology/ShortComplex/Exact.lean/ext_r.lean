import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem ext_r (s s' : S.Splitting) (h : s.r = s'.r) : s = s' := by
  have := CategoryTheory.ShortComplex.Splitting.epi_g s
  have eq := s.id
  rw [← s'.id, h, add_right_inj, cancel_epi S.g] at eq
  cases s
  congr

