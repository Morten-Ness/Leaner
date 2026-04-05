import Mathlib

open scoped Matrix

variable {R L M n ι ι' ιM : Type*}

variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable (φ : L →ₗ[R] Module.End R M)

variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

variable [Module.Finite R L] [Module.Free R L]

variable (x : L)

variable [IsDomain R]

theorem exists_isNilRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
    ∃ x : L, LinearMap.IsNilRegular φ x := by
  let b := chooseBasis R L
  let bₘ := chooseBasis R M
  let n := Fintype.card (ChooseBasisIndex R M)
  have aux :
    ((LinearMap.polyCharpoly φ b).coeff (LinearMap.nilRank φ)).IsHomogeneous (n - LinearMap.nilRank φ) :=
    LinearMap.polyCharpoly_coeff_isHomogeneous _ b (LinearMap.nilRank φ) (n - LinearMap.nilRank φ)
      (by simp [n, LinearMap.nilRank_le_card φ bₘ, finrank_eq_card_chooseBasisIndex])
  obtain ⟨x, hx⟩ : ∃ r, eval r ((LinearMap.polyCharpoly _ b).coeff (LinearMap.nilRank φ)) ≠ 0 := by
    by_contra! h₀
    apply LinearMap.polyCharpoly_coeff_nilRank_ne_zero φ b
    apply aux.eq_zero_of_forall_eval_eq_zero_of_le_card h₀ (le_trans _ h)
    simp only [n, finrank_eq_card_chooseBasisIndex, Nat.cast_le, Nat.sub_le]
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [LinearMap.isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ b, LinearEquiv.apply_symm_apply]

