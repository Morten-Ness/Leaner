import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (x : G₁) : (f.liftOfRightInverseAux f_inv hf g hg) (f x) = g x := by
  rw [MonoidHom.liftOfRightInverseAux]
  have hmem : f_inv (f x) * x⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    simp [map_mul, hf (f x)]
  have hker : f_inv (f x) * x⁻¹ ∈ g.ker := hg hmem
  rw [MonoidHom.mem_ker] at hker
  have h1 : g (f_inv (f x)) * g x⁻¹ = 1 := by
    simpa [map_mul, map_inv] using hker
  have h2 := congrArg (fun y => y * g x) h1
  simpa [mul_assoc] using h2
