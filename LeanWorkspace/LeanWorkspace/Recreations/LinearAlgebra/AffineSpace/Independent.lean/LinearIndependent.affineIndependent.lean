import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

theorem LinearIndependent.affineIndependent
    {v : ι → V} (hv : LinearIndependent k v) : AffineIndependent k v := by
  intro s w hw0 hwv i hi
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw0 0,
    Finset.weightedVSubOfPoint_apply] at hwv
  simp only [vsub_eq_sub, sub_zero] at hwv
  exact linearIndependent_iff'.mp hv s w hwv i hi

