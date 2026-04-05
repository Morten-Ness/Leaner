import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
  {M : Matrix m n R}

variable {B : (m → R) →ₗ[R] (n → R) →ₗ[R] R}

theorem _root_.Matrix.nondegenerate_toLinearMap₂'_iff :
    (toLinearMap₂' R M).Nondegenerate (R := R) ↔ M.Nondegenerate :=
  ⟨fun h ↦ ⟨separatingLeft_toLinearMap₂'_iff.mp h.1, separatingRight_toLinearMap₂'_iff.mp h.2⟩,
   fun h ↦ ⟨separatingLeft_toLinearMap₂'_iff.mpr h.1, separatingRight_toLinearMap₂'_iff.mpr h.2⟩⟩

