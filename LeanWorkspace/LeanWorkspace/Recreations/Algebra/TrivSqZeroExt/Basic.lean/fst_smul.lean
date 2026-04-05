import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem fst_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).fst = s • x.fst := rfl

