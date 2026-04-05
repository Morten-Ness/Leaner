import Mathlib

variable {ι F M N O G H : Type*}

variable [AddZeroClass M] [AddZeroClass N] {f : M → N} {g₁ g₂ : ι →₀ M}

theorem _root_.AddEquiv.finsuppUnique_symm {M : Type*} [AddZeroClass M] (d : M) :
    AddEquiv.finsuppUnique.symm d = single () d := by ext; simp [AddEquiv.finsuppUnique]

