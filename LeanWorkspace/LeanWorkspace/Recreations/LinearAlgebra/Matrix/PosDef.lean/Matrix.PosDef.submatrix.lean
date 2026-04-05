import Mathlib

variable {m n R R' : Type*}

variable [Ring R] [PartialOrder R] [StarRing R]

variable [CommRing R'] [PartialOrder R'] [StarRing R']

theorem submatrix {M : Matrix n n R} (hM : M.PosDef) {e : m → n}
    (he : Function.Injective e) : (M.submatrix e e).PosDef := by
  refine ⟨Matrix.PosSemidef.submatrix hM.1 _, fun x hx ↦ ?_⟩
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using
    hM.2 <| Finsupp.mapDomain_injective he |>.ne_iff' Finsupp.mapDomain_zero |>.2 hx

