FAIL
import Mathlib

variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

variable [FloorRing K]

theorem compExactValue_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
    (fract_a_ne_zero : Int.fract a ≠ 0) :
    ((⌊a⌋ : K) * b + c) / Int.fract a + b = (b * a + c) / Int.fract a := by
  have hfract : (Int.fract a : K) ≠ 0 := fract_a_ne_zero
  have ha : a = (⌊a⌋ : K) + Int.fract a := (Int.floor_add_fract a).symm
  rw [ha]
  calc
    ((⌊a⌋ : K) * b + c) / Int.fract a + b
        = (((⌊a⌋ : K) * b + c) + b * Int.fract a) / Int.fract a := by
            rw [add_div]
            field_simp [hfract]
            ring
    _ = (b * ((⌊a⌋ : K) + Int.fract a) + c) / Int.fract a := by
          congr 1
          ring
    _ = (b * a + c) / Int.fract a := by rw [ha]
