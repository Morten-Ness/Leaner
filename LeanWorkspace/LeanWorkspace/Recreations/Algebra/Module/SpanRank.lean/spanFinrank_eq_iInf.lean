import Mathlib

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

theorem spanFinrank_eq_iInf (p : Submodule R M) :
    p.spanFinrank = ⨅ (s : {s : Finset M // span R s = p}), s.1.card := by
  simp [Submodule.spanFinrank, Cardinal.toNat, Submodule.spanRank_toENat_eq_iInf_finset_card, ENat.iInf_toNat]

