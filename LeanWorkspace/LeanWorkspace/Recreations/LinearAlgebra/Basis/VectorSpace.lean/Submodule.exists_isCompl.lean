import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem Submodule.exists_isCompl (p : Submodule K V) : ∃ q : Submodule K V, IsCompl p q := ⟨LinearMap.ker p.subtype.leftInverse,
    LinearMap.isCompl_of_proj <| LinearMap.leftInverse_apply_of_inj p.ker_subtype⟩

