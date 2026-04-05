import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem embDomain_add (f : ι ↪ F) (v w : ι →₀ M) :
    embDomain f (v + w) = embDomain f v + embDomain f w := (Finsupp.embDomain.addMonoidHom f).map_add v w

