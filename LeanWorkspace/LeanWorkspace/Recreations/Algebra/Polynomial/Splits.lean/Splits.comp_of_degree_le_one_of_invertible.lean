import Mathlib

variable {R : Type*}

variable [CommSemiring R]

theorem Splits.comp_of_degree_le_one_of_invertible {f g : R[X]} (hf : f.Splits)
    (hg : g.degree ≤ 1) (h : Invertible g.leadingCoeff) : (f.comp g).Splits := hf.comp_of_natDegree_le_one_of_invertible (natDegree_le_of_degree_le hg) h

