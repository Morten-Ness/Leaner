import Mathlib

variable {α β : Type*} [LinearOrder α] [CommGroup β]
  (F : Finset (α × α)) {k : ℕ} (h : F.card = k) {a b : α}
  (g : α → β)

theorem Finset.prod_eq_prod_range_intervalGapsWithin (f : α → α → β) :
    ∏ z ∈ F, f z.1 z.2 = ∏ i ∈ range k,
      f (F.intervalGapsWithin h a b i).2 (F.intervalGapsWithin h a b i.succ).1 := by
  set p := F.intervalGapsWithin h a b
  symm
  apply prod_bij (fun (i : ℕ) hi ↦ ((p i).2, (p i.succ).1))
  · exact fun i _ ↦ F.intervalGapsWithin_mapsTo h a b (x := i) (by grind)
  · intro i hi j hj hij
    rw [mem_range] at hi hj
    apply F.intervalGapsWithin_injOn h a b <;> grind
  · intro z hz
    obtain ⟨i, hi₁, hi₂⟩ := F.intervalGapsWithin_surjOn h a b hz
    exact ⟨i, by grind, hi₂⟩
  · simp

