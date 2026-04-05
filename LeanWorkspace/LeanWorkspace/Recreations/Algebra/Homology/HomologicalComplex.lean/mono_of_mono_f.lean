import Mathlib

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

variable {c : ComplexShape ι} (C : HomologicalComplex V c)

theorem mono_of_mono_f {K L : HomologicalComplex V c} (φ : K ⟶ L)
    (hφ : ∀ i, Mono (φ.f i)) : Mono φ where
  right_cancellation g h eq := by
    ext i
    rw [← cancel_mono (φ.f i)]
    exact HomologicalComplex.congr_hom eq i

