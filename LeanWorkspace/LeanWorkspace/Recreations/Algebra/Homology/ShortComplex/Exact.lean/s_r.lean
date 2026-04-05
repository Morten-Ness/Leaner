import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

theorem s_r (s : S.Splitting) : s.s ≫ s.r = 0 := by
  have := CategoryTheory.ShortComplex.Splitting.epi_g s
  simp only [← cancel_epi S.g, comp_zero, g_s_assoc, sub_comp, id_comp,
    assoc, f_r, comp_id, sub_self]

