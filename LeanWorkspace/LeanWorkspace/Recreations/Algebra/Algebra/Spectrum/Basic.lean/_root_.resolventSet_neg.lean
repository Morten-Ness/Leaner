import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommRing R] [Ring A] [Algebra R A]

theorem _root_.resolventSet_neg (a : A) : resolventSet R (-a) = -resolventSet R a := Set.ext fun x => by
    simp only [mem_neg, spectrum.mem_resolventSet_iff, map_neg, ← neg_add', IsUnit.neg_iff, sub_neg_eq_add]

