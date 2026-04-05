import Mathlib

variable {R : Type*} [Semiring R] {C D : Type*} [Category* C] [Preadditive C]
  [Category* D] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  {ι : Type*} {c : ComplexShape ι}

variable {X Y : HomologicalComplex C c}

theorem units_smul_f_apply (r : Rˣ) (f : X ⟶ Y) (n : ι) : (r • f).f n = r • f.f n := rfl

