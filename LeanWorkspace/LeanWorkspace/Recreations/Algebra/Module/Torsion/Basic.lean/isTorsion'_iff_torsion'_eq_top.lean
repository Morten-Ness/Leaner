import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

variable (S : Type*) [CommMonoid S] [DistribMulAction S M] [SMulCommClass S R M]

theorem isTorsion'_iff_torsion'_eq_top : IsTorsion' M S ↔ Submodule.torsion' R M S = ⊤ := ⟨fun h => eq_top_iff.mpr fun _ _ => @h _, fun h x => by
    rw [← @Submodule.mem_torsion'_iff R, h]
    trivial⟩

