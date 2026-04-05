import Mathlib

variable {C ι : Type*} [Category* C] [Category* ι] [Abelian C]

variable (X : SpectralObject C ι)

set_option backward.isDefEq.respectTransparency false in
theorem isZero_H_obj_of_isIso {i j : ι} (f : i ⟶ j) (hf : IsIso f) (n : ℤ) :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let e : mk₁ (𝟙 i) ≅ mk₁ f := isoMk₁ (Iso.refl _) (asIso f) (by simp)
  refine IsZero.of_iso ?_ ((X.H n).mapIso e.symm)
  have h := X.zero₂ (𝟙 i) (𝟙 i) (𝟙 i) (by simp) n
  rw [← Functor.map_comp] at h
  rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← h]
  congr 1
  cat_disch

