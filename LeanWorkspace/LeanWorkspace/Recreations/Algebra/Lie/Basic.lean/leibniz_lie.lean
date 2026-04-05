import Mathlib

variable {L₁ L₂ M : Type*} [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M]

theorem leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) (m : M) :
    ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ := IsLieTower.leibniz_lie x y m

