import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
  {M : Matrix m n R}

variable {B : (m → R) →ₗ[R] (n → R) →ₗ[R] R}

theorem _root_.Matrix.separatingRight_toLinearMap₂'_iff :
    (toLinearMap₂' R M).SeparatingRight (R := R) ↔ M.SeparatingRight := by
  refine ⟨fun h ↦ separatingRight_def.mpr ?_, SeparatingRight.toLinearMap₂'⟩
  exact fun v hv => h v fun w => (M.toLinearMap₂'_apply' _ _).trans <| hv w

