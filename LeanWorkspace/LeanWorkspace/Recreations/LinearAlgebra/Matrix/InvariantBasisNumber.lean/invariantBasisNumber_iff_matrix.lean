import Mathlib

variable {R : Type*} [Semiring R]

theorem invariantBasisNumber_iff_matrix : InvariantBasisNumber R ↔ ∀ n m
    (f : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), f * g = 1 → g * f = 1 → n = m := (invariantBasisNumber_iff R).trans <| .intro (fun h n m f g hfg hgf ↦
      h (toLinearEquivRight'OfInv hfg hgf).symm) fun h n m e ↦ h n m (toMatrixRight' e)
    (toMatrixRight' e.symm) (by simp [← toMatrixRight'_comp]) (by simp [← toMatrixRight'_comp])

