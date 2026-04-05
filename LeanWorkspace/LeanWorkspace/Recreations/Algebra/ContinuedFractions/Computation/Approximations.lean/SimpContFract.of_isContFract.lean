import Mathlib

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

theorem SimpContFract.of_isContFract :
    (SimpContFract.of v).IsContFract := fun _ _ nth_partDen_eq =>
  lt_of_lt_of_le zero_lt_one (GenContFract.of_one_le_get?_partDen nth_partDen_eq)

