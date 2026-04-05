import Mathlib

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] (P : Polynomial R) {x : R}

theorem signVariations_neg : Polynomial.signVariations (-P) = Polynomial.signVariations P := by
  rw [Polynomial.signVariations, Polynomial.signVariations, coeffList_neg]
  simp only [List.map_map, List.filter_map]
  have hsc : SignType.sign ∘ (fun (x : R) => -x) = (fun x => -x) ∘ SignType.sign := by
    grind [Left.sign_neg]
  have h_neg_destutter (l : List SignType) :
      (l.destutter (¬· = ·)).map (- ·) = (l.map (- ·)).destutter (¬· = ·) := by
    grind [List.map_destutter, neg_inj]
  rw [hsc, List.comp_map, ← h_neg_destutter, List.length_map]
  congr 5
  funext
  simp [SignType.sign]

