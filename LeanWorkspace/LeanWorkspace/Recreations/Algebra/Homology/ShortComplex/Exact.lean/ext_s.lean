import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem ext_s (s s' : S.Splitting) (h : s.s = s'.s) : s = s' := by
  have := CategoryTheory.ShortComplex.Splitting.mono_f s
  have eq := s.id
  rw [← s'.id, h, add_left_inj, cancel_mono S.f] at eq
  cases s
  congr

