import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable {A B : Type*} [CommRing A] [CommRing B]

theorem filter_roots_map_range_eq_map_roots [IsDomain A] [IsDomain B] {f : A →+* B}
    [DecidablePred (· ∈ f.range)] (hf : Function.Injective f)
    (p : A[X]) : (p.map f).roots.filter (· ∈ f.range) = p.roots.map f := by
  classical
  ext b
  rw [Multiset.count_filter]
  split_ifs with h
  · obtain ⟨a, rfl⟩ := h
    simp [hf, Multiset.count_map_eq_count', Polynomial.eq_rootMultiplicity_map hf]
  · refine (Multiset.count_eq_zero.mpr fun h' ↦ h ?_).symm
    exact Exists.imp (fun _ ↦ And.right) <| Multiset.mem_map.mp h'

