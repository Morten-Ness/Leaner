import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem snd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) : (s • x).snd = s • x.snd := rfl

