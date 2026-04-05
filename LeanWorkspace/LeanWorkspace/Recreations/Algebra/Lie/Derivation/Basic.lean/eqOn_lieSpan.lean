import Mathlib

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

theorem eqOn_lieSpan {s : Set L} (h : Set.EqOn D1 D2 s) :
    Set.EqOn D1 D2 (LieSubalgebra.lieSpan R L s) := by
  intro _ hx
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx => exact h hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul t x _ hx => simp [hx]
  | lie x y _ _ hx hy => simp [hx, hy]

