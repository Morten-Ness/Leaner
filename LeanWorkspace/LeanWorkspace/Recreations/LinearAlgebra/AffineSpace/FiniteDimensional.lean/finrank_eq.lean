import Mathlib

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

