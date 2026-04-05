import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Subfield K}

variable {L : Type v} [Semiring L]

theorem eq_of_eqOn_of_field_closure_eq_top {s : Set K} (hs : Subfield.closure s = ⊤) {f g : K →+* L}
    (h : s.EqOn f g) : f = g := RingHom.eq_of_eqOn_subfield_top <| hs ▸ RingHom.eqOn_field_closure h

