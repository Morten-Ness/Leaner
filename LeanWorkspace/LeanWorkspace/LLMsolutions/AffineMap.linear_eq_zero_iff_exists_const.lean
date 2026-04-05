FAIL
import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

variable (k P1)

variable {k P1}

theorem linear_eq_zero_iff_exists_const (f : P1 →ᵃ[k] P2) :
    f.linear = 0 ↔ ∃ q, f = AffineMap.const k P1 q := by
  constructor
  · intro h
    by_cases hp : Nonempty P1
    · rcases hp with ⟨p0⟩
      refine ⟨f p0, ?_⟩
      ext p
      have hs := f.linear_vsub' p p0
      rw [h] at hs
      simpa using hs
    · exfalso
      exact hp <| AddTorsor.nonempty P1
  · rintro ⟨q, rfl⟩
    ext v
    rfl
