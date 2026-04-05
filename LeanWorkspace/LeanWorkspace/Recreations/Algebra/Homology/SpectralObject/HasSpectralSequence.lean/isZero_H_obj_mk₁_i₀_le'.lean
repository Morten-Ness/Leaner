import Mathlib

variable {C ι κ : Type*} [Category* C] [Abelian C] [Preorder ι]
  {c : ℤ → ComplexShape κ} {r₀ : ℤ}

variable (X : SpectralObject C ι) (data : SpectralSequenceDataCore ι c r₀)

variable [X.HasSpectralSequence data]

theorem isZero_H_obj_mk₁_i₀_le' (r r' : ℤ) (hrr' : r + 1 = r') (hr : r₀ ≤ r)
    (pq : κ) (hpq : ∀ (pq' : κ), ¬ ((c r).Rel pq pq'))
    (n : ℤ) (hn : n = data.deg pq + 1) (i₀' i₀ : ι)
    (hi₀' : i₀' = data.i₀ r' pq)
    (hi₀ : i₀ = data.i₀ r pq) :
    IsZero ((X.H n).obj (mk₁ (homOfLE (show i₀' ≤ i₀ by
      simpa only [hi₀', hi₀] using CategoryTheory.Abelian.SpectralObject.SpectralSequenceDataCore.i₀_le data r r' pq)))) := by
  subst hi₀' hi₀
  exact HasSpectralSequence.isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn

