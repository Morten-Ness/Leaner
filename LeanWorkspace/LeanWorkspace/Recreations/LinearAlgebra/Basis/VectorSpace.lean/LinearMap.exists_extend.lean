import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') :
    ∃ g : V →ₗ[K] V', g.comp p.subtype = f := let ⟨g, hg⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩

