import Mathlib

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

variable {M R : Type*} [Ring R] [Nontrivial R] [IsAddTorsionFree R]
  [AddCommGroup M] [Module R M] (A : AddSubgroup M) {ι : Type*} (b : Basis ι R M)

theorem addSubgroupOfClosure_apply (h : A = .closure (Set.range b)) (i : ι) :
    b.addSubgroupOfClosure A h i = b i := by
  simp [Module.Basis.addSubgroupOfClosure]

