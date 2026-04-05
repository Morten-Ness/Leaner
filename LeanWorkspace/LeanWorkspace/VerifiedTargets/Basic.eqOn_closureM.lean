import Mathlib

variable {M : Type*} {N : Type*}

variable {A : Type*}

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

variable [MulOneClass N]

theorem eqOn_closureM {f g : M →* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (Submonoid.closure s) := show Submonoid.closure s ≤ f.eqLocusM g from Submonoid.closure_le.2 h

