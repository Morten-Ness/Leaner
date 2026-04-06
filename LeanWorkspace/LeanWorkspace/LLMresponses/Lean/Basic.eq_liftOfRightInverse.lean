import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]

variable (f : G₁ →* G₂) (f_inv : G₂ → G₁)

theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : G₁ →* G₃)
    (hg : f.ker ≤ g.ker) (h : G₂ →* G₃) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  ext y
  have hhy : h (f (f_inv y)) = g (f_inv y) := by
    rw [← MonoidHom.comp_apply, hh]
  rw [hf y] at hhy
  simpa using hhy
