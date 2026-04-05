import Mathlib

variable {X G : Type*} {A B C : Set X}

variable [SMul G X]

theorem isDecompOn (f : Equidecomp X G) : Equidecomp.IsDecompOn f f.source f.witness := f.isDecompOn'.choose_spec

