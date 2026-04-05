import Mathlib

variable {M N : Type*} (μ : M → N → N) (r : N → N → Prop)

theorem contravariant_le_iff_contravariant_lt_and_eq [PartialOrder N] :
    Contravariant M N μ (· ≤ ·) ↔ Contravariant M N μ (· < ·) ∧ Contravariant M N μ (· = ·) := by
  refine ⟨fun h ↦ ⟨fun a b c bc ↦ ?_, fun a b c bc ↦ ?_⟩, fun h ↦ fun a b c bc ↦ ?_⟩
  · exact (h a bc.le).lt_of_ne (by rintro rfl; exact lt_irrefl _ bc)
  · exact (h a bc.le).antisymm (h a bc.ge)
  · exact bc.lt_or_eq.elim (fun bc ↦ (h.1 a bc).le) (fun bc ↦ (h.2 a bc).le)

