import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

theorem shape (i j : ι) (hij : ¬ c.Rel i j) :
    HomologicalComplex.homotopyCofiber.d φ i j = 0 := dif_neg hij

