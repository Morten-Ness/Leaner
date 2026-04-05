import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem LieAlgebra.ad_eq_lmul_left_sub_lmul_right (A : Type v) [Ring A] [Algebra R A] :
    (ad R A : A → Module.End R A) = LinearMap.mulLeft R - LinearMap.mulRight R := by
  ext a b; simp [LieRing.of_associative_ring_bracket]

