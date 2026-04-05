import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

theorem le₃₃' {r r' : ℤ} (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq' : κ)
    {i₃ i₃' : ι}
    (hi₃ : i₃ = data.i₃ r pq')
    (hi₃' : i₃' = data.i₃ r' pq') :
    i₃ ≤ i₃' := by
  simpa only [hi₃, hi₃'] using data.monotone_i₃ r r' pq'

