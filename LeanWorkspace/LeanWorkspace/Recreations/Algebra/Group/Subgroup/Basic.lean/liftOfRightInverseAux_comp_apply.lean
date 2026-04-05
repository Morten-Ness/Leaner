import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (x : G₁) : (f.liftOfRightInverseAux f_inv hf g hg) (f x) = g x := by
  dsimp [MonoidHom.liftOfRightInverseAux]
  rw [← mul_inv_eq_one, ← g.map_inv, ← g.map_mul, ← g.mem_ker]
  apply hg
  rw [f.mem_ker, f.map_mul, f.map_inv, mul_inv_eq_one]
  simp only [hf _]

