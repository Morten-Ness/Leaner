import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [Group G] [MulAction G X]

theorem right_inv {f : Equidecomp X G} {x : X} (h : x ∈ f.target) :
    f (f.toPartialEquiv.symm x) = x := by simp [h]

