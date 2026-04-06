import Mathlib

variable {α : Type u}

variable {M : Type*}

variable [Monoid M] {a b c : M}

theorem isUnit_iff_mulLeft_bijective {a : M} :
    IsUnit a ↔ Function.Bijective (a * ·) := by
  constructor
  · rintro ⟨u, rfl⟩
    refine Function.bijective_iff_has_inverse.mpr ?_
    refine ⟨(↑u⁻¹ * ·), ?_, ?_⟩
    · intro x
      simp
    · intro x
      simp
  · intro h
    rcases h with ⟨hinj, hsurj⟩
    rcases hsurj 1 with ⟨b, hb⟩
    have hba : b * a = 1 := by
      apply hinj
      calc
        a * (b * a) = (a * b) * a := by simp [mul_assoc]
        _ = 1 * a := by simpa using congrArg (fun x => x * a) hb
        _ = a := by simp
        _ = a * 1 := by simp
    exact ⟨⟨a, b, hb, hba⟩, rfl⟩
