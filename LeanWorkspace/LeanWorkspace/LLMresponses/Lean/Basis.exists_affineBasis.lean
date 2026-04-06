FAIL
import Mathlib

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

variable (k V P)

theorem exists_affineBasis : ∃ (s : Set P) (b : AffineBasis (↥s) k P), ⇑b = ((↑) : s → P) := by
  classical
  obtain ⟨b⟩ := AffineIndependent.exists_affineBasis (k := k) (P := P) (s := (Set.univ : Set P))
    (by simpa [Set.affineSpan_univ] using (submodule_span_eq : Submodule.span k (Set.univ : Set V) = ⊤))
  refine ⟨Set.range b, b.reindex (Equiv.ofInjective b b.injective), ?_⟩
  ext x
  rfl
