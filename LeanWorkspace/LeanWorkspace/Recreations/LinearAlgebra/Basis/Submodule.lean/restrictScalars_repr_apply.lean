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

theorem restrictScalars_repr_apply (m : span R (Set.range b)) (i : ι) :
    algebraMap R S ((b.restrictScalars R).repr m i) = b.repr m i := by
  suffices
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ (b.restrictScalars R).repr.toLinearMap =
      ((b.repr : M →ₗ[S] ι →₀ S).restrictScalars R).domRestrict _
    by exact DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Module.Basis.ext (b.restrictScalars R) fun _ => ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply, map_one,
    Module.Basis.repr_self, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, LinearMap.domRestrict_apply,
    Module.Basis.restrictScalars_apply, LinearMap.coe_restrictScalars]

