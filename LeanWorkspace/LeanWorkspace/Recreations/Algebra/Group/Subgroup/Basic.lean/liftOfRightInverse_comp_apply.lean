import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ →* G₃ // f.ker ≤ g.ker }) (x : G₁) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x := MonoidHom.liftOfRightInverseAux_comp_apply f f_inv hf g.1 g.2 x

