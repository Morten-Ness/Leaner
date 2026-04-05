import Mathlib

variable {R : Type*}

variable [Ring R] (p q : R[X])

theorem neg_cancelLeads : -p.cancelLeads q = q.cancelLeads p := neg_sub _ _

