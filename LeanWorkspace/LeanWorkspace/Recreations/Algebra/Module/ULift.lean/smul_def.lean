import Mathlib

variable {R : Type u} {M : Type v} {N : Type w}

theorem smul_def [SMul R M] (s : ULift R) (x : M) : s • x = s.down • x := rfl

