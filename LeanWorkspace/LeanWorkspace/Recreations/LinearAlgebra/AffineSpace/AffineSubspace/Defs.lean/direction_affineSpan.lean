import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem direction_affineSpan (s : Set P) : (affineSpan k s).direction = vectorSpan k s := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro v ⟨p₁, ⟨p₂, hp₂, v₁, hv₁, hp₁⟩, p₃, ⟨p₄, hp₄, v₂, hv₂, hp₃⟩, rfl⟩
    simp only [SetLike.mem_coe]
    rw [hp₁, hp₃, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc]
    exact
      (vectorSpan k s).sub_mem ((vectorSpan k s).add_mem hv₁ (vsub_mem_vectorSpan k hp₂ hp₄)) hv₂
  · exact vectorSpan_mono k (subset_spanPoints k s)

