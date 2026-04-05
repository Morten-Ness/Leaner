import Mathlib

variable {ι κ M N P : Type*}

variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

theorem _root_.Subsingleton.mulSupport_eq [Subsingleton M] (f : ι → M) : Function.mulSupport f = ∅ := Function.mulSupport_eq_empty_iff.mpr <| Subsingleton.elim f 1

