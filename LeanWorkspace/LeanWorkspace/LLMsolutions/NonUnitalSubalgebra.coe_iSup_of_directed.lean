FAIL
import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

variable {ι : Sort*}

theorem coe_iSup_of_directed [Nonempty ι] {S : ι → NonUnitalSubalgebra R A}
    (dir : Directed (· ≤ ·) S) : ↑(iSup S) = ⋃ i, (S i : Set A) := by
  classical
  rw [Set.ext_iff]
  intro x
  change x ∈ iSup S ↔ x ∈ ⋃ i, (S i : Set A)
  rw [show iSup S = sSup (Set.range S) by simp [iSup]]
  change x ∈ sSup (Set.range S) ↔ x ∈ ⋃ i, (S i : Set A)
  rw [NonUnitalSubalgebra.mem_sSup_of_directed]
  · simp only [Set.mem_range, Set.mem_iUnion, exists_exists_and_eq_and]
  · intro a ha b hb
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    rcases dir i j with ⟨k, hik, hjk⟩
    exact ⟨S k, ⟨k, rfl⟩, hik, hjk⟩
