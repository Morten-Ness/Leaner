import Mathlib

variable {L₁ L₂ M : Type*} [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M]

theorem lie_swap_lie [Bracket L₂ L₁] [AddCommGroup M] [IsLieTower L₁ L₂ M] [IsLieTower L₂ L₁ M]
    (x : L₁) (y : L₂) (m : M) : ⁅⁅x, y⁆, m⁆ = -⁅⁅y, x⁆, m⁆ := by
  have h1 := leibniz_lie x y m
  have h2 := leibniz_lie y x m
  convert congr($h1.symm - $h2) using 1 <;> simp only [add_sub_cancel_right, sub_add_cancel_right]

