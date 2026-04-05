import Mathlib

variable {ι ι' R R₂ M M' : Type*}

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

variable {M R : Type*} [Ring R] [Nontrivial R] [IsAddTorsionFree R]
  [AddCommGroup M] [Module R M] (A : AddSubgroup M) {ι : Type*} (b : Basis ι R M)

theorem addSubgroupOfClosure_repr_apply (h : A = .closure (Set.range b)) (x : A) (i : ι) :
    (b.addSubgroupOfClosure A h).repr x i = b.repr x i := by
  suffices Finsupp.mapRange.linearMap (Algebra.linearMap ℤ R) ∘ₗ
      (b.addSubgroupOfClosure A h).repr.toLinearMap =
        ((b.repr : M →ₗ[R] ι →₀ R).restrictScalars ℤ).domRestrict A.toIntSubmodule by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  exact (b.addSubgroupOfClosure A h).ext fun _ ↦ by simp

