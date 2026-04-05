import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem fst_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).fst = s • x.fst := rfl

