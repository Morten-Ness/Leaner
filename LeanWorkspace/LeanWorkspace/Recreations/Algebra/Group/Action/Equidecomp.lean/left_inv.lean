import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem left_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f.toPartialEquiv.symm (f x) = x := by simp [h]

