import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem LinearMap.exists_extend_of_notMem {p : Submodule K V} {v : V} (f : p →ₗ[K] V')
    (hv : v ∉ p) (y : V') : ∃ g : V →ₗ[K] V', g.comp p.subtype = f ∧ g v = y := by
  rcases (LinearPMap.supSpanSingleton ⟨p, f⟩ v y hv).toFun.exists_extend with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · ext x
    have := LinearPMap.supSpanSingleton_apply_mk_of_mem ⟨p, f⟩ y hv x.2
    simpa using congr($hg _).trans this
  · have := LinearPMap.supSpanSingleton_apply_self ⟨p, f⟩ y hv
    simpa using congr($hg _).trans this

