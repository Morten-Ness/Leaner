import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

theorem le₂₃' (r : ℤ) (hr : r₀ ≤ r) (pq' : κ)
    {i₂ i₃ : ι}
    (hi₂ : i₂ = data.i₂ pq')
    (hi₃ : i₃ = data.i₃ r pq') :
    i₂ ≤ i₃ := by
  simpa only [hi₂, hi₃] using data.le₂₃ r pq'

