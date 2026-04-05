import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)

variable [X.HasSpectralSequence data]

theorem isZero_H_obj_mk₁_i₃_le' (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq' pq))
    (n : ℤ) (hn : n = data.deg pq - 1) (i₃ i₃' : ι)
    (hi₃ : i₃ = data.i₃ r pq)
    (hi₃' : i₃' = data.i₃ r' pq) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (show i₃ ≤ i₃' by
      simpa only [hi₃, hi₃'] using CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₃_le data r r' pq)))) := by
  subst hi₃ hi₃'
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn

