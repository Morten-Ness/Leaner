import Mathlib

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

variable {S : Type*} [CommRing R] [IsDomain R] [Ring S] [Nontrivial S] [AddCommGroup M]

variable [Algebra R S] [Module S M] [Module R M]

variable [IsScalarTower R S M] [IsTorsionFree R S] (b : Basis ι S M)

theorem mem_span_iff_repr_mem (m : M) :
    m ∈ span R (Set.range b) ↔ ∀ i, b.repr m i ∈ Set.range (algebraMap R S) := by
  refine
    ⟨fun hm i => ⟨(b.restrictScalars R).repr ⟨m, hm⟩ i, Module.Basis.restrictScalars_repr_apply b R ⟨m, hm⟩ i⟩,
      fun h => ?_⟩
  rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply S _]
  refine sum_mem fun i _ => ?_
  obtain ⟨_, h⟩ := h i
  simp_rw [← h, algebraMap_smul]
  exact smul_mem _ _ (subset_span (Set.mem_range_self i))

