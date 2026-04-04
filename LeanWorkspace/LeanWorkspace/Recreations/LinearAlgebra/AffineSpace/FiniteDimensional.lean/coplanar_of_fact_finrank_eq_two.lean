import Mathlib

variable {k : Type*} {V : Type*} {P : Type*}

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]

variable (k) in

theorem coplanar_of_fact_finrank_eq_two (s : Set P) [h : Fact (finrank k V = 2)] : Coplanar k s := coplanar_of_finrank_eq_two s h.out

