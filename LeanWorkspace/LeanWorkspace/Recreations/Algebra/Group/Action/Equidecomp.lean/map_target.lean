import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem map_target {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f.symm x ∈ f.source := f.toPartialEquiv.map_target h

