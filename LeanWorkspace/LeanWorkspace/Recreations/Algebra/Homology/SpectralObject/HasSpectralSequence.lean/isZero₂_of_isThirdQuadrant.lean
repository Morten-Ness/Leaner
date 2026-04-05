import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)

variable [X.HasSpectralSequence data]

variable (Y : SpectralObject C EInt)

variable [Y.IsThirdQuadrant]

theorem isZero₂_of_isThirdQuadrant (i j : EInt) (hij : i ≤ j) (n : ℤ) (hj : j ≤ n) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) := IsThirdQuadrant.isZero₂ i j hij n hj

