import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

theorem toMatrix_mk (i j : n) (hij : i ≠ j) (c : R) :
    Matrix.TransvectionStruct.toMatrix ⟨i, j, hij, c⟩ = Matrix.transvection i j c := rfl

