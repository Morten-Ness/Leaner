import Mathlib

variable {M G : Type*} [AddCancelCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]
    [LocallyFiniteOrder M] [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

theorem LocallyFiniteOrder.orderAddMonoidHom_bijective [Nontrivial G] :
    Function.Bijective (orderAddMonoidHom G) := by
  refine ⟨orderAddMonoidHom_strictMono.injective, ?_⟩
  suffices 1 ∈ (orderAddMonoidHom G).range by
    obtain ⟨x, hx⟩ := this
    exact fun a ↦ ⟨a • x, by simp_all⟩
  have ⟨a, ha⟩ := exists_zero_lt (α := G)
  obtain ⟨b, hb⟩ := exists_covBy_of_wellFoundedLT (α := Icc 0 a) (a := ⟨0, by simpa using ha.le⟩)
    (fun H ↦ ha.not_ge (@H ⟨a, by simpa using ha.le⟩ ha.le))
  use b.1
  have : 0 ≤ b.1 := hb.1.le
  suffices Ico 0 b.1 = {0} by simpa [orderAddMonoidHom, addMonoidHom, this]
  ext x
  simp only [mem_Ico, mem_singleton]
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra hx'
    have := b.2
    simp only [Finset.mem_Icc] at this
    exact hb.2 (c := ⟨x, by simpa [h₁] using h₂.le.trans this.2⟩)
      (lt_of_le_of_ne h₁ (by simpa using Ne.symm hx')) h₂
  · rintro rfl
    simpa using hb.1

