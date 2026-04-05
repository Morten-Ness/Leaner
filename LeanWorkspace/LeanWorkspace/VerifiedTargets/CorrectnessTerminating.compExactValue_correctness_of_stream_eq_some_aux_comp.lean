import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

variable [FloorRing K]

theorem compExactValue_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
    (fract_a_ne_zero : Int.fract a ≠ 0) :
    ((⌊a⌋ : K) * b + c) / Int.fract a + b = (b * a + c) / Int.fract a := by
  field_simp
  rw [Int.fract]
  ring

