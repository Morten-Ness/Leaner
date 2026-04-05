import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

variable (F : C ⥤ D) [F.Additive]

theorem preservesFiniteColimits_iff_forall_exact_map_and_epi :
    PreservesFiniteColimits F ↔
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Epi (F.map S.g) := (CategoryTheory.Functor.preservesFiniteColimits_tfae F).out 3 0

