import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

variable [CommRing T]

theorem rootSet_maps_to' {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] (hp : p.map (algebraMap T S') = 0 → p.map (algebraMap T S) = 0)
    (f : S →ₐ[T] S') : (p.rootSet S).MapsTo f (p.rootSet S') := fun x hx => by
  rw [Polynomial.mem_rootSet'] at hx ⊢
  rw [aeval_algHom, AlgHom.comp_apply, hx.2, _root_.map_zero]
  exact ⟨mt hp hx.1, rfl⟩

