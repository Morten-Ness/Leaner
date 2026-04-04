import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem affineIndependent_of_subsingleton [Subsingleton ι] (p : ι → P) : AffineIndependent k p := fun _ _ h _ i hi => Fintype.eq_of_subsingleton_of_sum_eq h i hi

