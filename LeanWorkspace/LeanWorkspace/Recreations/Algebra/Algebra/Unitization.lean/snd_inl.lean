import Mathlib

variable {R A : Type*}

theorem snd_inl [Zero A] (r : R) : (Unitization.inl r : Unitization R A).snd = 0 := rfl

