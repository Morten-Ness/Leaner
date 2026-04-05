import Mathlib

open scoped RightActions

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

theorem snd_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).snd = s • x.snd := rfl

