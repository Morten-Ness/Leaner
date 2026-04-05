import Mathlib

variable (R : Type u) (X : Type v) [CommRing R]

variable {L : Type w} [LieRing L] [LieAlgebra R L]

theorem liftAux_spec (f : X → L) (a b : lib R X) (h : FreeLieAlgebra.Rel R X a b) :
    FreeLieAlgebra.liftAux R f a = FreeLieAlgebra.liftAux R f b := by
  induction h with
  | lie_self a' => simp only [FreeLieAlgebra.liftAux_map_mul, map_zero, lie_self]
  | leibniz_lie a' b' c' =>
    simp only [FreeLieAlgebra.liftAux_map_mul, FreeLieAlgebra.liftAux_map_add, sub_add_cancel, lie_lie]
  | smul b' _ h₂ => simp only [FreeLieAlgebra.liftAux_map_smul, h₂]
  | add_right c' _ h₂ => simp only [FreeLieAlgebra.liftAux_map_add, h₂]
  | mul_left c' _ h₂ => simp only [FreeLieAlgebra.liftAux_map_mul, h₂]
  | mul_right c' _ h₂ => simp only [FreeLieAlgebra.liftAux_map_mul, h₂]

