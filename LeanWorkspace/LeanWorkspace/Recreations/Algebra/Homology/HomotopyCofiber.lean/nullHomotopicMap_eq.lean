import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι} {F G K : HomologicalComplex C c} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ] [DecidableRel c.Rel]

variable [∀ i, HasBinaryBiproduct (K.X i) (K.X i)]
  [HasHomotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K))]

variable (hc : ∀ j, ∃ i, c.Rel i j)

theorem nullHomotopicMap_eq : HomologicalComplex.cylinder.πCompι₀Homotopy.nullHomotopicMap K = HomologicalComplex.cylinder.π K ≫ HomologicalComplex.cylinder.ι₀ K - 𝟙 _ := by
  ext i
  by_cases hi : c.Rel i (c.next i)
  · exact HomologicalComplex.homotopyCofiber.ext_from_X HomologicalComplex.homotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K)) (c.next i) i hi
      (HomologicalComplex.cylinder.πCompι₀Homotopy.inlX_nullHomotopy_f _ _ _ _) (HomologicalComplex.cylinder.πCompι₀Homotopy.inrX_nullHomotopy_f _ hc _)
  · exact HomologicalComplex.homotopyCofiber.ext_from_X' HomologicalComplex.homotopyCofiber (biprod.lift (𝟙 K) (-𝟙 K)) _ hi (HomologicalComplex.cylinder.πCompι₀Homotopy.inrX_nullHomotopy_f _ hc _)

