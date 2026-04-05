import Mathlib

open scoped RightActions

variable {R R₁ S₁ R₂ S₂ M₁ M₂ M₁' M₂' N₂ n m n' m' ι : Type*}

variable [CommRing R] [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
  {M : Matrix m n R}

variable {B : (m → R) →ₗ[R] (n → R) →ₗ[R] R}

theorem separatingRight_toMatrix₂'_iff :
    (toMatrix₂' R B).SeparatingRight ↔ B.SeparatingRight := separatingRight_toLinearMap₂'_iff.symm.trans
    <| (toLinearMap₂'_toMatrix' (R := R) B).symm ▸ Iff.rfl

