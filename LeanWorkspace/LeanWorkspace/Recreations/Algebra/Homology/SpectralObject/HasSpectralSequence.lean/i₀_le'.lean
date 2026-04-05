import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

theorem i₀_le' {r r' : ℤ} (hrr' : r + 1 = r') (hr : r₀ ≤ r) (pq' : κ)
    {i₀' i₀ : ι} (hi₀' : i₀' = data.i₀ r' pq') (hi₀ : i₀ = data.i₀ r pq') :
    i₀' ≤ i₀ := by
  rw [hi₀', hi₀]
  exact data.antitone_i₀ r r' pq'

