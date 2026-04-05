import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem mulSupport_disjoint_iff : Disjoint (Function.mulSupport f) s ↔ EqOn f 1 s := by
  simp_rw [← subset_compl_iff_disjoint_right, Function.mulSupport_subset_iff', notMem_compl_iff, EqOn,
    Pi.one_apply]

