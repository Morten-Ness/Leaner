import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)

variable [X.HasSpectralSequence data]

theorem isZero_H_obj_mk₁_i₀_le (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : ℤ) (hn : n = data.deg pq + 1) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_le data r r' pq)))) := HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

