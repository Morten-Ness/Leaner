import Mathlib

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

theorem free_shortExact_rank_add [Module.Free R S.X₁] [Module.Free R S.X₃]
    [StrongRankCondition R] :
    Module.rank R S.X₂ = Module.rank R S.X₁ + Module.rank R S.X₃ := by
  haveI := ModuleCat.free_shortExact hS'
  rw [Module.Free.rank_eq_card_chooseBasisIndex, Module.Free.rank_eq_card_chooseBasisIndex R S.X₁,
    Module.Free.rank_eq_card_chooseBasisIndex R S.X₃, Cardinal.add_def, Cardinal.eq]
  exact ⟨Module.Basis.indexEquiv (Module.Free.chooseBasis R S.X₂) (ModuleCat.Basis.ofShortExact hS'
    (Module.Free.chooseBasis R S.X₁) (Module.Free.chooseBasis R S.X₃))⟩

