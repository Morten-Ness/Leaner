import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem LinearMap.leftInverse_comp_of_inj {f : V →ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) :
    f.leftInverse ∘ₗ f = LinearMap.id := by
  simpa [leftInverse, h_inj] using (f.exists_leftInverse_of_injective h_inj).choose_spec

