import Mathlib

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']

variable {v : ι → V} {s t : Set V} {x y z : V}

theorem Submodule.exists_le_ker_of_notMem {p : Submodule K V} {v : V} (hv : v ∉ p) :
    ∃ f : V →ₗ[K] K, f v ≠ 0 ∧ p ≤ ker f := by
  rcases LinearMap.exists_extend_of_notMem (0 : p →ₗ[K] K) hv 1 with ⟨f, hpf, hfv⟩
  refine ⟨f, by simp [hfv], fun x hx ↦ ?_⟩
  simpa using congr($hpf ⟨x, hx⟩)

