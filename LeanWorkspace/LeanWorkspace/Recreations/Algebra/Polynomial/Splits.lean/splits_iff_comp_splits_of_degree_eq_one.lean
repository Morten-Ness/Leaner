import Mathlib

variable {R : Type*}

variable [Field R] {f g : R[X]}

theorem splits_iff_comp_splits_of_degree_eq_one {f g : R[X]} (hg : g.degree = 1) :
    f.Splits ↔ (f.comp g).Splits := Polynomial.splits_iff_comp_splits_of_natDegree_eq_one (natDegree_eq_of_degree_eq_some hg)

