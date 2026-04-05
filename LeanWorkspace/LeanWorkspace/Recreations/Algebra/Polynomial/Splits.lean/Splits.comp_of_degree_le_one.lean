import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem Splits.comp_of_degree_le_one {f g : R[X]} (hf : f.Splits) (hg : g.degree ≤ 1) :
    (f.comp g).Splits := hf.comp_of_natDegree_le_one (natDegree_le_of_degree_le hg)

