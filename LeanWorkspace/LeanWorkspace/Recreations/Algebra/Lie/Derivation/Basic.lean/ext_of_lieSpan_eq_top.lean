import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

theorem ext_of_lieSpan_eq_top (s : Set L) (hs : LieSubalgebra.lieSpan R L s = ⊤)
    (h : Set.EqOn D1 D2 s) : D1 = D2 := LieDerivation.ext fun _ => LieDerivation.eqOn_lieSpan h <| hs.symm ▸ trivial

