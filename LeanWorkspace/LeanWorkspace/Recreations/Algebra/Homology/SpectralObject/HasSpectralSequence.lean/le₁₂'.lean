import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

theorem le₁₂' (pq' : κ) {i₁ i₂ : ι} (hi₁ : i₁ = data.i₁ pq') (hi₂ : i₂ = data.i₂ pq') :
    i₁ ≤ i₂ := by
  simpa only [hi₁, hi₂] using data.le₁₂ pq'

