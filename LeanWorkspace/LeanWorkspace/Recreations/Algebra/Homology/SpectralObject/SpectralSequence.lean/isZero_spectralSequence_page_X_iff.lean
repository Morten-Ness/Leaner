import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  (X : SpectralObject C ι)
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

variable [X.HasSpectralSequence data]

theorem isZero_spectralSequence_page_X_iff (r : ℤ) (hr : r₀ ≤ r) (pq : κ)
    (i₀ i₁ i₂ i₃ : ι) (h₀ : i₀ = data.i₀ r pq) (h₁ : i₁ = data.i₁ pq)
    (h₂ : i₂ = data.i₂ pq) (h₃ : i₃ = data.i₃ r pq)
    (n₀ n₁ n₂ : ℤ) (h : n₁ = data.deg pq) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsZero (((X.spectralSequence data).page r).X pq) ↔
      IsZero (X.E (homOfLE (data.le₀₁' r hr pq h₀ h₁))
        (homOfLE (data.le₁₂' pq h₁ h₂))
        (homOfLE (data.le₂₃' r hr pq h₂ h₃)) n₀ n₁ n₂) :=
  Iso.isZero_iff (X.spectralSequencePageXIso data r hr pq i₀ i₁ i₂ i₃
    h₀ h₁ h₂ h₃ n₀ n₁ n₂ h)

