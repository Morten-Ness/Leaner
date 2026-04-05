import Mathlib

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem apply_coe_mem_map (f : M →ₙ* N) (S : Subsemigroup M) (x : S) : f x ∈ S.map f := Subsemigroup.mem_map_of_mem f x.prop

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem bot_prod_bot : (⊥ : Subsemigroup M).prod (⊥ : Subsemigroup N) = ⊥ := SetLike.coe_injective <| by simp [Subsemigroup.coe_prod]

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_equiv_eq_map_symm (f : N ≃* M) (K : Subsemigroup M) :
    K.comap (f : N →ₙ* M) = K.map (f.symm : M →ₙ* N) := (Subsemigroup.map_equiv_eq_comap_symm f.symm K).symm

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_iInf {ι : Sort*} (f : M →ₙ* N) (s : ι → Subsemigroup N) :
    (iInf s).comap f = ⨅ i, (s i).comap f := (Subsemigroup.gc_map_comap f).u_iInf

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_inf (S T : Subsemigroup N) (f : M →ₙ* N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f := (Subsemigroup.gc_map_comap f).u_inf

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_map_comap {S : Subsemigroup N} {f : M →ₙ* N} :
    ((S.comap f).map f).comap f = S.comap f := (Subsemigroup.gc_map_comap f).u_l_u_eq_u _

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem comap_top (f : M →ₙ* N) : (⊤ : Subsemigroup N).comap f = ⊤ := (Subsemigroup.gc_map_comap f).u_top

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem gc_map_comap (f : M →ₙ* N) : GaloisConnection (Subsemigroup.map f) (Subsemigroup.comap f) := fun _ _ =>
  Subsemigroup.map_le_iff_le_comap

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem le_comap_map {f : M →ₙ* N} : S ≤ (S.map f).comap f := (Subsemigroup.gc_map_comap f).le_u_l _

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_bot (f : M →ₙ* N) : (⊥ : Subsemigroup M).map f = ⊥ := (Subsemigroup.gc_map_comap f).l_bot

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_comap_le {S : Subsemigroup N} {f : M →ₙ* N} : (S.comap f).map f ≤ S := (Subsemigroup.gc_map_comap f).l_u_le _

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_comap_map {f : M →ₙ* N} : ((S.map f).comap f).map f = S.map f := (Subsemigroup.gc_map_comap f).l_u_l_eq_l _

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_equiv_eq_comap_symm (f : M ≃* N) (K : Subsemigroup M) :
    K.map (f : M →ₙ* N) = K.comap (f.symm : N →ₙ* M) := SetLike.coe_injective (f.toEquiv.image_eq_preimage_symm K)

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_equiv_top (f : M ≃* N) : (⊤ : Subsemigroup M).map (f : M →ₙ* N) = ⊤ := SetLike.coe_injective <| Set.image_univ.trans f.surjective.range_eq

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_inf (S T : Subsemigroup M) (f : M →ₙ* N) (hf : Function.Injective f) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem map_sup (S T : Subsemigroup M) (f : M →ₙ* N) : (S ⊔ T).map f = S.map f ⊔ T.map f := (Subsemigroup.gc_map_comap f).l_sup

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem mem_map_equiv {f : M ≃* N} {K : Subsemigroup M} {x : N} :
    x ∈ K.map (f : M →ₙ* N) ↔ f.symm x ∈ K := @Set.mem_image_equiv _ _ (K : Set M) f.toEquiv x

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem monotone_comap {f : M →ₙ* N} : Monotone (Subsemigroup.comap f) := (Subsemigroup.gc_map_comap f).monotone_u

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem monotone_map {f : M →ₙ* N} : Monotone (Subsemigroup.map f) := (Subsemigroup.gc_map_comap f).monotone_l

end

section

variable {M N P σ : Type*}

variable [Mul M] [Mul N] [Mul P] (S : Subsemigroup M)

theorem top_prod_top : (⊤ : Subsemigroup M).prod (⊤ : Subsemigroup N) = ⊤ := (Subsemigroup.top_prod _).trans <| Subsemigroup.comap_top _

end
