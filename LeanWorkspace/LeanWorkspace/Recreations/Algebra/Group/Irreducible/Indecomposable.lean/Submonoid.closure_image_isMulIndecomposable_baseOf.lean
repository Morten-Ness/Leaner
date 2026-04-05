import Mathlib

variable {ι M G S : Type*} [Monoid M] [CommGroup G] [LinearOrder S]

theorem Submonoid.closure_image_isMulIndecomposable_baseOf [Finite ι]
    [CommMonoid S] [IsOrderedCancelMonoid S]
    (v : ι → M) (f : M →* S) :
    closure (v '' IsMulIndecomposable.baseOf v f) = closure (v '' {i | 1 < f (v i)}) := by
  refine le_antisymm (closure_mono (image_mono <| IsMulIndecomposable.baseOf_subset_one_lt v f))
    (closure_le.mpr ?_)
  rintro - ⟨i, hi : 1 < f (v i), rfl⟩
  by_contra hi'
  let t : Set ι := {i | IsMulIndecomposable v {j | 1 < f (v j)} i}
  let s : Set ι := {j | 1 < f (v j) ∧ v j ∉ closure (v '' t)}
  have hne : s.Nonempty := ⟨i, hi, hi'⟩
  clear! i
  obtain ⟨i, hi⟩ := s.toFinite.exists_minimalFor (f ∘ v) s hne
  have ⟨(hi₀ : 1 < f (v i)), (hi₁ : v i ∉ _)⟩ : i ∈ s := hi.prop
  have hi₂ (k : ι) (hk₀ : 1 < f (v k)) (hk₁ : f (v k) < f (v i)) : v k ∈ closure (v '' t) := by
    by_contra hk₂; exact not_le.mpr hk₁ <| hi.le_of_le ⟨hk₀, hk₂⟩ hk₁.le
  have hi₃ : i ∉ t := by contrapose! hi₁; exact subset_closure <| mem_image_of_mem v hi₁
  obtain ⟨j, k, hj, hk, hjk⟩ : ∃ (j k : ι) (hj : 1 < f (v j)) (hk : 1 < f (v k)),
      v i = v j * v k := by
    grind [IsMulIndecomposable]
  have hj' : v j ∈ closure (v '' t) := hi₂ j hj <| by aesop
  have hk' : v k ∈ closure (v '' t) := hi₂ k hk <| by aesop
  replace hjk : v i ∈ closure (v '' t) := hjk ▸ mul_mem hj' hk'
  exact hi₁ hjk

