import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem GenContFract.of_isSimpContFract :
    (of v).IsSimpContFract := fun _ _ nth_partNum_eq =>
  GenContFract.of_partNum_eq_one nth_partNum_eq

