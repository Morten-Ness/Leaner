import Mathlib

variable {T : Type*} {S : Type*} {R : Type*} {A : Type*}

theorem toProd_smul [SMul S R] [SMul S A] (s : S) (x : Unitization R A) :
    (s • x).toProd = s • x.toProd := rfl

