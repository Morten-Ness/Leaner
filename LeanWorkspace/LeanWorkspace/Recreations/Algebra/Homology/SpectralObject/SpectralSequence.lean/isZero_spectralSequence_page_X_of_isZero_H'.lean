import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

variable [X.HasSpectralSequence data]

theorem isZero_spectralSequence_page_X_of_isZero_H' (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (h : IsZero ((X.H (data.deg pq)).obj (mk₁ (homOfLE (data.le₁₂ pq))))) :
    IsZero (((X.spectralSequence data).page r).X pq) := X.isZero_spectralSequence_page_X_of_isZero_H data r hr pq _ rfl _ _ rfl rfl h

unseal CategoryTheory.Abelian.SpectralObject.spectralSequence in

