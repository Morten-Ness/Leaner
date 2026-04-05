import Mathlib

variable {R A B : Type*}

theorem snd_mul [Semiring R] (x y : R[ε]) : snd (x * y) = fst x * snd y + snd x * fst y := rfl

