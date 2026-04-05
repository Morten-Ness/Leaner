import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n]
  {R : Type v} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem toGLPos_injective : Function.Injective (Matrix.SpecialLinearGroup.toGLPos : Matrix.SpecialLinearGroup n R → Matrix.GLPos n R) := -- Porting note: had to rewrite this to hint the correct types to Lean
  -- (It can't find the coercion Matrix.GLPos n R → Matrix n n R)
  Function.Injective.of_comp
    (f := fun (A : Matrix.GLPos n R) ↦ ((A : GL n R) : Matrix n n R))
    Subtype.coe_injective

