import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable (hc : ∀ j, ∃ i, c.Rel i j)

theorem inrCompHomotopy_hom (i j : ι) (hij : c.Rel j i) :
    (HomologicalComplex.homotopyCofiber.inrCompHomotopy φ hc).hom i j = HomologicalComplex.homotopyCofiber.inlX φ i j hij := dif_pos hij

