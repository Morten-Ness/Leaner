import Mathlib

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem comap_comap (s : AffineSubspace k P₃) (f : P₁ →ᵃ[k] P₂) (g : P₂ →ᵃ[k] P₃) :
    (s.comap g).comap f = s.comap (g.comp f) := rfl

-- lemmas about AffineSubspace.map and AffineSubspace.comap derived from the Galois connection

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem comap_inf (s t : AffineSubspace k P₂) (f : P₁ →ᵃ[k] P₂) :
    (s ⊓ t).comap f = s.comap f ⊓ t.comap f := (AffineSubspace.gc_map_comap f).u_inf

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem comap_map_eq_of_injective {f : P₁ →ᵃ[k] P₂} (hf : Function.Injective f)
    (s : AffineSubspace k P₁) : (s.map f).comap f = s := (AffineSubspace.gciMapComap hf).u_l_eq _

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem comap_span (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) :
    (affineSpan k s).comap (f : P₁ →ᵃ[k] P₂) = affineSpan k (f ⁻¹' s) := by
  rw [← AffineSubspace.map_symm, AffineSubspace.map_span, AffineEquiv.coe_coe, f.image_symm]

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem comap_supr {ι : Sort*} (f : P₁ →ᵃ[k] P₂) (s : ι → AffineSubspace k P₂) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (AffineSubspace.gc_map_comap f).u_iInf

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem direction_affineSpan_insert {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) :
    (affineSpan k (insert p₂ (s : Set P))).direction =
    Submodule.span k {p₂ -ᵥ p₁} ⊔ s.direction := by
  rw [sup_comm, ← Set.union_singleton, ← AffineSubspace.coe_affineSpan_singleton k V p₂]
  change (s ⊔ affineSpan k {p₂}).direction = _
  rw [AffineSubspace.direction_sup hp₁ (mem_affineSpan k (Set.mem_singleton _)), direction_affineSpan]
  simp

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem direction_affineSpan_pair_le_iff_exists_smul {p₁ q₁ p₂ q₂ : P} :
    line[k, p₁, q₁].direction ≤ line[k, p₂, q₂].direction ↔ ∃ z : k, z • (q₂ -ᵥ p₂) = q₁ -ᵥ p₁ := by
  rw [direction_affineSpan, direction_affineSpan, vectorSpan_pair_rev, vectorSpan_pair_rev,
    Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]

end

section

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem direction_sup_eq_sup_direction {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p ∈ s₁)
    (hp₂ : p ∈ s₂) : (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction := by
  rw [AffineSubspace.direction_sup hp₁ hp₂]
  simp

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem eqOn_affineSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ →ᵃ[k] P₂}
    (h_agree : s.EqOn f g) : Set.EqOn f g (affineSpan k s) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨q, hq⟩; · simp
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, AffineMap.linear_eqOn_vectorSpan h_agree hy]

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem gc_map_comap (f : P₁ →ᵃ[k] P₂) : GaloisConnection (AffineSubspace.map f) (AffineSubspace.comap f) := fun _ _ =>
  AffineSubspace.map_le_iff_le_comap

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem le_comap_map (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₁) : s ≤ (s.map f).comap f := (AffineSubspace.gc_map_comap f).le_u_l _

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem linear_eqOn_vectorSpan {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]
    {s : Set P₁} {f g : P₁ →ᵃ[k] P₂}
    (h_agree : s.EqOn f g) : Set.EqOn f.linear g.linear (vectorSpan k s) := by
  simp only [vectorSpan_def]
  apply LinearMap.eqOn_span
  rintro - ⟨x, hx, y, hy, rfl⟩
  simp [h_agree hx, h_agree hy]

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem map_comap_le (f : P₁ →ᵃ[k] P₂) (s : AffineSubspace k P₂) : (s.comap f).map f ≤ s := (AffineSubspace.gc_map_comap f).l_u_le _

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem map_inf_le (s₁ s₂ : AffineSubspace k P₁) : (s₁ ⊓ s₂).map f ≤ s₁.map f ⊓ s₂.map f := le_inf (AffineSubspace.map_mono _ inf_le_left) (AffineSubspace.map_mono _ inf_le_right)

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

theorem map_sup (s t : AffineSubspace k P₁) (f : P₁ →ᵃ[k] P₂) : (s ⊔ t).map f = s.map f ⊔ t.map f := (AffineSubspace.gc_map_comap f).l_sup

end

section

variable {k V₁ P₁ V₂ P₂ V₃ P₃ : Type*} [Ring k]

variable [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁]

variable [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂]

variable [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃]

variable (f : P₁ →ᵃ[k] P₂)

theorem span_eq_top_of_surjective {s : Set P₁} (hf : Function.Surjective f)
    (h : affineSpan k s = ⊤) : affineSpan k (f '' s) = ⊤ := by
  rw [← AffineSubspace.map_span, h, AffineMap.map_top_of_surjective f hf]

end
