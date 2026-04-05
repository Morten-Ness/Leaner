import Mathlib

variable {A : Type u} [Ring A] {M : Type v} [AddCommGroup M] [Module A M]

variable (pres : Presentation A M)

theorem finite [Finite pres.G] :
    Module.Finite A M := Finite.of_surjective _ pres.surjective_π

