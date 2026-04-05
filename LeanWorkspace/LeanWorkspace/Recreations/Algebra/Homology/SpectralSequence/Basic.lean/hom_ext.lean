import Mathlib

variable (C : Type*) [Category C] [Abelian C]
  {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ : ℤ)

theorem hom_ext {E E' : CategoryTheory.SpectralSequence C c r₀} {f f' : E ⟶ E'}
    (h : ∀ (r : ℤ) (hr : r₀ ≤ r), f.hom r = f'.hom r) :
    f = f' := Hom.ext (by grind)

attribute [simp] id_hom
attribute [reassoc, simp] comp_hom

