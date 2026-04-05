import Mathlib

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem exists_affineBasis_of_finiteDimensional [Fintype ι] [FiniteDimensional k V]
    (h : Fintype.card ι = Module.finrank k V + 1) : Nonempty (AffineBasis ι k P) := by
  obtain ⟨s, b, hb⟩ := AffineBasis.exists_affineBasis k V P
  lift s to Finset P using AffineBasis.finite_set b
  refine ⟨b.reindex <| Fintype.equivOfCardEq ?_⟩
  rw [h, ← AffineBasis.card_eq_finrank_add_one b]

