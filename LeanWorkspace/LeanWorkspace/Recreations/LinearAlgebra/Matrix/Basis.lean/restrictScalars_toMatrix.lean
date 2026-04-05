import Mathlib

variable {ι ι' κ κ' : Type*}

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

variable (e : Basis ι R M) (v : ι' → M) (i : ι) (j : ι')

theorem restrictScalars_toMatrix [Fintype ι] [DecidableEq ι] {S : Type*} [CommRing S] [Nontrivial S]
    [Algebra R₂ S] [Module S M₂] [IsScalarTower R₂ S M₂] [IsDomain R₂] [IsTorsionFree R₂ S]
    (b : Module.Basis ι S M₂) (v : ι → span R₂ (Set.range b)) :
    (algebraMap R₂ S).mapMatrix ((b.restrictScalars R₂).toMatrix v) =
      b.toMatrix (fun i ↦ (v i : M₂)) := by
  ext
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply,
    Module.Basis.restrictScalars_repr_apply, Module.Basis.toMatrix_apply]

