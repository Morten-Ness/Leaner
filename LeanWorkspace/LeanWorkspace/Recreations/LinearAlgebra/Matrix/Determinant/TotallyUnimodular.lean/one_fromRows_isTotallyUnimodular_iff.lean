import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem one_fromRows_isTotallyUnimodular_iff [DecidableEq n] (A : Matrix m n R) :
    (fromRows (1 : Matrix n n R) A).IsTotallyUnimodular ↔ A.IsTotallyUnimodular := by
  have hA :
    fromRows (1 : Matrix n n R) A =
      (fromRows A (1 : Matrix n n R)).reindex (Equiv.sumComm m n) (Equiv.refl n) := by
    aesop
  rw [hA, Matrix.reindex_isTotallyUnimodular, Matrix.fromRows_one_isTotallyUnimodular_iff]

