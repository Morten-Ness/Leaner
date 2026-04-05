import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem epi_of_epi_f {K L : HomologicalComplex V c} (φ : K ⟶ L)
    (hφ : ∀ i, Epi (φ.f i)) : Epi φ where
  left_cancellation g h eq := by
    ext i
    rw [← cancel_epi (φ.f i)]
    exact HomologicalComplex.congr_hom eq i

