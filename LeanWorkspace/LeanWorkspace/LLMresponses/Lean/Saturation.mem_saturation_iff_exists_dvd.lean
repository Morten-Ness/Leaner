FAIL
import Mathlib

variable {M : Type*}

variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

theorem mem_saturation_iff_exists_dvd : x ∈ s.saturation ↔ ∃ m ∈ s, x ∣ m := by
  constructor
  · intro hx
    rcases (Submonoid.mem_saturation_iff.mp hx) with ⟨n, hn⟩
    refine ⟨x ^ n, hn, ?_⟩
    refine ⟨x ^ (n - 1), ?_⟩
    cases n with
    | zero =>
        simp
    | succ n =>
        simp [pow_succ', mul_comm, mul_left_comm, mul_assoc]
  · rintro ⟨m, hm, ⟨a, rfl⟩⟩
    apply Submonoid.mem_saturation_iff.mpr
    refine ⟨2, ?_⟩
    simpa [pow_succ', mul_assoc] using s.mul_mem hm hm
