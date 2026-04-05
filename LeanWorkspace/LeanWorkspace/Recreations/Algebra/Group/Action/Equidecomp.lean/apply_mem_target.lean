import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [SMul G X]

theorem apply_mem_target {f : Equidecomp X G} {x : X} (h : x ∈ f.source) :
    f x ∈ f.target := by simp [h]

