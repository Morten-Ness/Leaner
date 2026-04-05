import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n : ℤ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem isZero_opcycles (h : IsZero ((X.H n).obj (mk₁ f))) :
    IsZero (X.opcycles f g n) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_epi (X.pOpcycles ..)]
  apply h.eq_of_src

