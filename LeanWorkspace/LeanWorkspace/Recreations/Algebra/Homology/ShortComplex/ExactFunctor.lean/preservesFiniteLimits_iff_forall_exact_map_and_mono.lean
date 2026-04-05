import Mathlib

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

variable (F : C ⥤ D) [F.Additive]

theorem preservesFiniteLimits_iff_forall_exact_map_and_mono :
    PreservesFiniteLimits F ↔
      ∀ (S : ShortComplex C), S.ShortExact → (S.map F).Exact ∧ Mono (F.map S.f) := (CategoryTheory.Functor.preservesFiniteLimits_tfae F).out 3 0

