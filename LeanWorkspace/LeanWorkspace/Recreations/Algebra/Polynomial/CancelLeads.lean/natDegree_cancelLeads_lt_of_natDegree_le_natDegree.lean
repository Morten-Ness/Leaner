import Mathlib

variable {R : Type*}

variable [CommRing R] {p q : R[X]}

theorem natDegree_cancelLeads_lt_of_natDegree_le_natDegree (h : p.natDegree ≤ q.natDegree)
    (hq : 0 < q.natDegree) : (p.cancelLeads q).natDegree < q.natDegree := Polynomial.natDegree_cancelLeads_lt_of_natDegree_le_natDegree_of_comm (mul_comm _ _) h hq

