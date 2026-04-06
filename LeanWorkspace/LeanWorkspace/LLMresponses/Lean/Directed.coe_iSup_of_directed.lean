FAIL
import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A)

variable {ι : Type*} [Nonempty ι] {K : ι → Subalgebra R A}

theorem coe_iSup_of_directed (dir : Directed (· ≤ ·) K) : ↑(iSup K) = ⋃ i, (K i : Set A) := by
  classical
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    let L : Subalgebra R A := sSup (Set.range K)
    have hL : L = iSup K := by
      apply le_antisymm
      · refine sSup_le ?_
        rintro _ ⟨i, rfl⟩
        exact le_iSup K i
      · refine iSup_le ?_
        intro i
        exact le_sSup ⟨i, rfl⟩
    have hx' : x ∈ L := by simpa [L, hL] using hx
    refine Subalgebra.sSup_induction (s := Set.range K) (p := fun y => ∃ i, y ∈ K i) ?hS ?h0 ?h1 ?hmul ?hsmul hx'
    · rintro _ ⟨i, rfl⟩ hy
      exact ⟨i, hy⟩
    · exact Classical.choice ‹Nonempty ι› |> fun i => ⟨i, (K i).zero_mem⟩
    · rintro a b ⟨i, ha⟩ ⟨j, hb⟩
      rcases dir i j with ⟨k, hik, hjk⟩
      exact ⟨k, (K k).add_mem (hik ha) (hjk hb)⟩
    · rintro a b ⟨i, ha⟩ ⟨j, hb⟩
      rcases dir i j with ⟨k, hik, hjk⟩
      exact ⟨k, (K k).mul_mem (hik ha) (hjk hb)⟩
    · intro r a ha
      rcases ha with ⟨i, ha⟩
      exact ⟨i, (K i).algebraMap_mem r ▸ (K i).mul_mem ((K i).algebraMap_mem r) ha⟩
  · rintro ⟨i, hx⟩
    exact show x ∈ iSup K from le_iSup K i hx
