import Mathlib

variable {R : Type*} {a b : R}

variable [Zero R] [One R]

theorem omega_re : (ω : QuadraticAlgebra R a b).re = 0 := rfl

