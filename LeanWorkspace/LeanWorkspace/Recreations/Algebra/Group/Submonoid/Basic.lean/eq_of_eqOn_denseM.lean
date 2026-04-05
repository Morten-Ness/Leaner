import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable [MulOneClass N]

theorem eq_of_eqOn_denseM {s : Set M} (hs : Submonoid.closure s = ⊤) {f g : M →* N} (h : s.EqOn f g) :
    f = g := eq_of_eqOn_topM <| hs ▸ MonoidHom.eqOn_closureM h

