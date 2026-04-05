import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem rootSet_mapsTo {p : T[X]} [IsDomain T] {S S' : Type*} [CommRing S] [IsDomain S] [Algebra T S]
    [CommRing S'] [IsDomain S'] [Algebra T S'] [Module.IsTorsionFree T S'] (f : S →ₐ[T] S') :
    (p.rootSet S).MapsTo f (p.rootSet S') := by
  refine Polynomial.rootSet_maps_to' (fun h₀ => ?_) f
  obtain rfl : p = 0 :=
    map_injective _ (FaithfulSMul.algebraMap_injective T S') (by rwa [Polynomial.map_zero])
  exact Polynomial.map_zero _

