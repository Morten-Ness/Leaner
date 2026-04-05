import Mathlib

variable {K : Type u} {L : Type v} {M : Type w}

variable [DivisionRing K] [DivisionRing L] [DivisionRing M]

variable {s : Set K}

variable {K : Type u} [Field K] (s : Subfield K)

private def commClosure (s : Set K) : Subfield K where
  carrier := {z : K | ∃ x ∈ Subring.closure s, ∃ y ∈ Subring.closure s, x / y = z}
  zero_mem' := ⟨0, Subring.zero_mem _, 1, Subring.one_mem _, div_one _⟩
  one_mem' := ⟨1, Subring.one_mem _, 1, Subring.one_mem _, div_one _⟩
  neg_mem' {x} := by
    rintro ⟨y, hy, z, hz, x_eq⟩
    exact ⟨-y, Subring.neg_mem _ hy, z, hz, x_eq ▸ neg_div _ _⟩
  inv_mem' x := by rintro ⟨y, hy, z, hz, x_eq⟩; exact ⟨z, hz, y, hy, x_eq ▸ (inv_div _ _).symm⟩
  add_mem' x_mem y_mem := by
    -- Use `id` in the next 2 `obtain`s so that assumptions stay there for the `rwa`s below
    obtain ⟨nx, hnx, dx, hdx, rfl⟩ := id x_mem
    obtain ⟨ny, hny, dy, hdy, rfl⟩ := id y_mem
    by_cases hx0 : dx = 0; · rwa [hx0, div_zero, zero_add]
    by_cases hy0 : dy = 0; · rwa [hy0, div_zero, add_zero]
    exact
      ⟨nx * dy + dx * ny, Subring.add_mem _ (Subring.mul_mem _ hnx hdy) (Subring.mul_mem _ hdx hny),
        dx * dy, Subring.mul_mem _ hdx hdy, (div_add_div nx ny hx0 hy0).symm⟩
  mul_mem' := by
    rintro _ _ ⟨nx, hnx, dx, hdx, rfl⟩ ⟨ny, hny, dy, hdy, rfl⟩
    exact ⟨nx * ny, Subring.mul_mem _ hnx hny, dx * dy, Subring.mul_mem _ hdx hdy,
      (div_mul_div_comm _ _ _ _).symm⟩


private theorem commClosure_eq_closure {s : Set K} : commClosure s = Subfield.closure s := le_antisymm
    (fun _ ⟨_, hy, _, hz, eq⟩ ↦ eq ▸ div_mem (Subfield.subring_closure_le s hy) (Subfield.subring_closure_le s hz))
    (Subfield.closure_le.mpr fun x hx ↦ ⟨x, Subring.subset_closure hx, 1, Subring.one_mem _, div_one x⟩)


theorem mem_closure_iff {s : Set K} {x} :
    x ∈ Subfield.closure s ↔ ∃ y ∈ Subring.closure s, ∃ z ∈ Subring.closure s, y / z = x := by
  rw [← commClosure_eq_closure]; rfl

