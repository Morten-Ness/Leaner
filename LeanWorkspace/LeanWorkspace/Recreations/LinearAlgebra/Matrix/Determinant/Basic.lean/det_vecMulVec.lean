import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_vecMulVec [Nontrivial n] (u v : n → R) : (vecMulVec u v).det = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  let uv' := ((vecMulVec u v).updateRow i v).updateRow j v
  have huv' : uv'.det = 0 := by
    refine Matrix.detRowAlternating.map_eq_zero_of_eq _ ?_ hij
    simp [uv', hij]
  have : vecMulVec u v =
      (uv'.updateRow i (u i • uv' i)).updateRow j (u j • uv'.updateRow i (u i • uv' i) j) := by
    unfold uv'
    rw [updateRow_comm _ hij, updateRow_idem, updateRow_ne hij.symm, updateRow_ne hij,
      updateRow_self, updateRow_self, updateRow_comm _ hij, updateRow_idem,
      ← update_vecMulVec u v j, update_eq_self, ← update_vecMulVec u v i, update_eq_self]
  rw [this, Matrix.det_updateRow_smul, updateRow_eq_self, Matrix.det_updateRow_smul, updateRow_eq_self, huv',
    mul_zero, mul_zero]

