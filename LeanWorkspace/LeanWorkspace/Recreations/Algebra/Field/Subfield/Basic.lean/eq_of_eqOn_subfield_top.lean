import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

variable {L : Type v} [Semiring L]

theorem eq_of_eqOn_subfield_top {f g : K →+* L} (h : Set.EqOn f g (⊤ : Subfield K)) : f = g := ext fun _ => h trivial

