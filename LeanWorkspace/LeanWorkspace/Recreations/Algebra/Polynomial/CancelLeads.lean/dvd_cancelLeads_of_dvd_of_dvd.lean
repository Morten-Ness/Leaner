import Mathlib

open scoped Polynomial

variable {R : Type*}

variable [CommRing R] {p q : R[X]}

theorem dvd_cancelLeads_of_dvd_of_dvd {r : R[X]} (pq : p ∣ q) (pr : p ∣ r) : p ∣ q.cancelLeads r := dvd_sub (pr.trans (Dvd.intro_left _ rfl)) (pq.trans (Dvd.intro_left _ rfl))

