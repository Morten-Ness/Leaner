import Mathlib

variable {k E PE : Type*} [Field k] [AddCommGroup E] [Module k E] [AddTorsor E PE]

theorem LinearMap.slope_comp {F : Type*} [AddCommGroup F] [Module k F] (f : E →ₗ[k] F) (g : k → E)
    (a b : k) : slope (f ∘ g) a b = f (slope g a b) := f.toAffineMap.slope_comp g a b

