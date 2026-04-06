FAIL
import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

theorem ext_linear_iff {f g : P1 →ᵃ[k] P2} : f = g ↔ (f.linear = g.linear) ∧ (∃ p, f p = g p) := by
  constructor
  · intro h
    subst h
    refine ⟨rfl, ?_⟩
    rcases isEmpty_or_nonempty P1 with hP1 | hP1
    · exfalso
      exact hP1.false (by infer_instance)
    · rcases hP1 with ⟨p⟩
      exact ⟨p, rfl⟩
  · rintro ⟨hlin, ⟨p, hp⟩⟩
    ext q
    calc
      f q = f.linear (q -ᵥ p) +ᵥ f p := by
        simp using (vadd_vsub_assoc (f p) q p)
      _ = g.linear (q -ᵥ p) +ᵥ f p := by simp [hlin]
      _ = g.linear (q -ᵥ p) +ᵥ g p := by rw [hp]
      _ = g q := by
        simp using (vadd_vsub_assoc (g p) q p).symm
