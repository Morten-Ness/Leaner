import Mathlib

variable {R S M : Type*}

variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMul S R] [IsScalarTower S R M]

variable {p q : Submodule R M}

set_option backward.privateInPublic true in
private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p := Set.biInter_subset_of_mem


set_option backward.privateInPublic true in
private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S := Set.subset_iInter₂


theorem subsingleton_iff : Subsingleton (Submodule R M) ↔ Subsingleton M := have h : Subsingleton (Submodule R M) ↔ Subsingleton (AddSubmonoid M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← toAddSubmonoid_inj,
      Submodule.bot_toAddSubmonoid, Submodule.top_toAddSubmonoid]
  h.trans AddSubmonoid.subsingleton_iff

