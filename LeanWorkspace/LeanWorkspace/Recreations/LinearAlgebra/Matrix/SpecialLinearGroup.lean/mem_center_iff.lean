import Mathlib

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R]

variable {S : Type*} [CommRing S]

theorem mem_center_iff {A : Matrix.SpecialLinearGroup n R} :
    A ∈ center (Matrix.SpecialLinearGroup n R) ↔ ∃ (r : R), r ^ (Fintype.card n) = 1 ∧ scalar n r = A := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩; · exact ⟨by aesop, by simp [Subsingleton.elim A 1]⟩
  refine ⟨fun h ↦ ⟨A i i, ?_, ?_⟩, fun ⟨r, _, hr⟩ ↦ Subgroup.mem_center_iff.mpr fun B ↦ ?_⟩
  · have : det ((scalar n) (A i i)) = 1 := (Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center h i).symm ▸ A.property
    simpa using this
  · exact Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center h i
  · suffices ↑ₘ(B * A) = ↑ₘ(A * B) from Subtype.val_injective this
    simpa only [Matrix.SpecialLinearGroup.coe_mul, ← hr] using (scalar_commute (n := n) r (Commute.all r) B).symm

