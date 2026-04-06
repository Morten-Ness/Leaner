FAIL
import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem exists_affine_subbasis {t : Set P} (ht : affineSpan k t = ⊤) :
    ∃ s ⊆ t, ∃ b : AffineBasis s k P, ⇑b = ((↑) : s → P) := by
  classical
  let b : AffineBasis (Set.univ : Set P) k P := by
    classical
    simpa using (AffineBasis.ofEq (k := k) (P := P) (s := (Set.univ : Set P)) (by ext x; simp))
  refine ⟨t, Set.Subset.rfl, ?_, ?_⟩
  · simpa [ht] using b.reindex (Equiv.Set.univ t)
  · ext x
    rfl
