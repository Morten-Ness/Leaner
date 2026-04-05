import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

theorem le₀₁' (r : ℤ) (hr : r₀ ≤ r) (pq' : κ) {i₀ i₁ : ι}
    (hi₀ : i₀ = data.i₀ r pq')
    (hi₁ : i₁ = data.i₁ pq') :
    i₀ ≤ i₁ := by
  have := data.le₀₁ r pq'
  simpa only [hi₀, hi₁] using data.le₀₁ r pq'

