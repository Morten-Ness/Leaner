import Mathlib

variable {R : Type*} {a b : R}

variable [Zero R] [One R]

theorem omega_im : (ω : QuadraticAlgebra R a b).im = 1 := rfl

