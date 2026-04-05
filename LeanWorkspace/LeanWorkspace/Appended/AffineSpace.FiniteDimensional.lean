import Mathlib

section

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem card_eq_finrank_add_one [Fintype ι] (b : AffineBasis ι k P) :
    Fintype.card ι = Module.finrank k V + 1 := have : FiniteDimensional k V := AffineBasis.finiteDimensional b
  b.ind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp b.tot

end

section

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem exists_affineBasis_of_finiteDimensional [Fintype ι] [FiniteDimensional k V]
    (h : Fintype.card ι = Module.finrank k V + 1) : Nonempty (AffineBasis ι k P) := by
  obtain ⟨s, b, hb⟩ := AffineBasis.exists_affineBasis k V P
  lift s to Finset P using AffineBasis.finite_set b
  refine ⟨b.reindex <| Fintype.equivOfCardEq ?_⟩
  rw [h, ← AffineBasis.card_eq_finrank_add_one b]

end

section

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem finite [FiniteDimensional k V] (b : AffineBasis ι k P) : Finite ι := finite_of_fin_dim_affineIndependent k b.ind

end

section

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem finiteDimensional [Finite ι] (b : AffineBasis ι k P) : FiniteDimensional k V := let ⟨i⟩ := b.nonempty
  (b.basisOf i).finiteDimensional_of_finite

end

section

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [AddTorsor V P]

variable [DivisionRing k] [Module k V]

theorem finite_set [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P) :
    s.Finite := finite_set_of_fin_dim_affineIndependent k b.ind

end

section

variable {R S V W P : Type*} [Ring R] [Ring S]
  [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V] [AddTorsor V P]
  [AddCommGroup W] [Module R W] [Module S W] [Module.Finite S W] [SMulCommClass R S W]

theorem finrank_eq [Module.Free S W] [StrongRankCondition R] [StrongRankCondition S] :
    Module.finrank S (P →ᵃ[R] W) = (Module.finrank R V + 1) * Module.finrank S W := calc
    _ = Module.finrank S (V →ᵃ[R] W) :=
      have ⟨p⟩ : Nonempty P := inferInstance
      AffineEquiv.vaddConst R p |>.symm.congrLeftₗ S W |>.finrank_eq
    _ = Module.finrank S (W × (V →ₗ[R] W)) := (AffineMap.toConstProdLinearMap S).finrank_eq
    _ = (Module.finrank R V + 1) * Module.finrank S W := by
      rw [Module.finrank_prod, Module.finrank_linearMap]
      ring

end
