import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (data : SpectralSequenceDataCore ι c r₀)

theorem i₀_le (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    data.i₀ r' pq ≤ data.i₀ r pq :=
  data.antitone_i₀ r r' pq

