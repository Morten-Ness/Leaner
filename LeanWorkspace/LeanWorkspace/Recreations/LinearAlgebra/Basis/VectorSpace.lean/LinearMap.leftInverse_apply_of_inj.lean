import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem LinearMap.leftInverse_apply_of_inj {f : V →ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V) :
    f.leftInverse (f x) = x := LinearMap.ext_iff.mp (f.leftInverse_comp_of_inj h_inj) x

