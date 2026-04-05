import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [∀ x : M, Decidable (x = 0)]

theorem exists_isTorsionBy {p : R} (hM : IsTorsion' M <| Submonoid.powers p) (d : ℕ) (hd : d ≠ 0)
    (s : Fin d → M) (hs : span R (Set.range s) = ⊤) :
    ∃ j : Fin d, Module.IsTorsionBy R M (p ^ Submodule.pOrder hM (s j)) := by
  let oj := List.argmax (fun i => Submodule.pOrder hM <| s i) (List.finRange d)
  have hoj : oj.isSome :=
    Option.ne_none_iff_isSome.mp fun eq_none =>
      hd <| List.finRange_eq_nil_iff.mp <| List.argmax_eq_none.mp eq_none
  use Option.get _ hoj
  rw [Module.isTorsionBy_iff_torsionBy_eq_top, eq_top_iff, ← hs, Submodule.span_le,
    Set.range_subset_iff]
  intro i; change (p ^ Submodule.pOrder hM (s (Option.get oj hoj))) • s i = 0
  have : Submodule.pOrder hM (s i) ≤ Submodule.pOrder hM (s <| Option.get _ hoj) :=
    List.le_of_mem_argmax (List.mem_finRange i) (Option.get_mem hoj)
  rw [← Nat.sub_add_cancel this, pow_add, mul_smul, Submodule.pow_pOrder_smul, smul_zero]

