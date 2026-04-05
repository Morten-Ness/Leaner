import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)

variable [X.HasSpectralSequence data]

variable (Y : SpectralObject C EInt)

variable [Y.IsFirstQuadrant]

theorem isZero₁_of_isFirstQuadrant (i j : EInt) (hij : i ≤ j) (hj : j ≤ (0 : ℤ)) (n : ℤ) :
    IsZero ((Y.H n).obj (mk₁ (homOfLE hij))) := IsFirstQuadrant.isZero₁ i j hij  hj n

