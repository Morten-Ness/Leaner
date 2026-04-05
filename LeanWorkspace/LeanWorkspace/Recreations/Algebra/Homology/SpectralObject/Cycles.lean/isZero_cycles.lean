import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ)

theorem isZero_cycles (h : IsZero ((X.H n).obj (mk₁ g))) :
    IsZero (X.cycles f g n) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (X.iCycles ..)]
  apply h.eq_of_tgt

