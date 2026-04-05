import Mathlib

section

variable {M N G H α β γ δ : Type*}

variable [SMul M α]

theorem Commute.smul_right [Mul α] [SMulCommClass M α α] [IsScalarTower M α α] {a b : α}
    (h : Commute a b) (r : M) : Commute a (r • b) := (mul_smul_comm _ _ _).trans ((congr_arg _ h).trans <| (smul_mul_assoc _ _ _).symm)

end

section

variable {M N G H α β γ δ : Type*}

theorem Function.Injective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N β] {f : α → β} (hf : Function.Injective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N α where
  smul_comm c₁ c₂ x := hf <| by simp only [h₁, h₂, smul_comm c₁ c₂ (f x)]

end

section

variable {M N G H α β γ δ : Type*}

theorem Function.Surjective.smulCommClass [SMul M α] [SMul N α] [SMul M β] [SMul N β]
    [SMulCommClass M N α] {f : α → β} (hf : Function.Surjective f) (h₁ : ∀ (c : M) x, f (c • x) = c • f x)
    (h₂ : ∀ (c : N) x, f (c • x) = c • f x) : SMulCommClass M N β where
  smul_comm c₁ c₂ := hf.forall.2 fun x ↦ by simp only [← h₁, ← h₂, smul_comm c₁ c₂ x]

end

section

variable {M N G H α β γ δ : Type*}

variable (G P : Type*)

theorem IsCancelSMul.eq_one_of_smul {G P} [Monoid G] [MulAction G P] [IsCancelSMul G P] {g : G}
    {x : P} (h : g • x = x) : g = 1 := IsCancelSMul.right_cancel g 1 x ((one_smul G x).symm ▸ h)

end

section

variable {M N G H α β γ δ : Type*}

variable (G P : Type*)

theorem IsCancelSMul.left_cancel {G P} [SMul G P] [IsCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c → b = c := IsLeftCancelSMul.left_cancel' a b c

end

section

variable {M N G H α β γ δ : Type*}

theorem IsCentralScalar.unop_smul_eq_smul {M α : Type*} [SMul M α] [SMul Mᵐᵒᵖ α]
    [IsCentralScalar M α] (m : Mᵐᵒᵖ) (a : α) : MulOpposite.unop m • a = m • a := by
  induction m; exact (IsCentralScalar.op_smul_eq_smul _ a).symm

export IsCentralVAdd (op_vadd_eq_vadd unop_vadd_eq_vadd)
export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)

attribute [simp] IsCentralScalar.op_smul_eq_smul

-- these instances are very low priority, as there is usually a faster way to find these instances

end

section

variable {M N G H α β γ δ : Type*}

variable (G P : Type*)

theorem IsLeftCancelSMul.left_cancel {G P} [SMul G P] [IsLeftCancelSMul G P] (a : G) (b c : P) :
    a • b = a • c → b = c := IsLeftCancelSMul.left_cancel' a b c

end

section

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem IsScalarTower.of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] [SMulCommClass R₁ R R] : IsScalarTower R₁ R R where
  smul_assoc x₁ y z := by rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← smul_comm, smul_eq_mul,
    mul_comm, ← smul_eq_mul]

end

section

variable {M N G H α β γ δ : Type*}

theorem IsScalarTower.of_smul_one_mul {M N} [Monoid N] [SMul M N]
    (h : ∀ (x : M) (y : N), x • (1 : N) * y = x • y) : IsScalarTower M N N := ⟨fun x y z ↦ by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩

end

section

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem SMulCommClass.of_commMonoid
    (A B G : Type*) [CommMonoid G] [SMul A G] [SMul B G]
    [IsScalarTower A G G] [IsScalarTower B G G] :
    SMulCommClass A B G where
  smul_comm r s x := by
    rw [← one_smul G (s • x), ← smul_assoc, ← one_smul G x, ← smul_assoc s 1 x,
      smul_comm, smul_assoc, one_smul, smul_assoc, one_smul]

end

section

variable {M N G H α β γ δ : Type*}

theorem SMulCommClass.of_mul_smul_one {M N} [Monoid N] [SMul M N]
    (H : ∀ (x : M) (y : N), y * x • (1 : N) = x • y) : SMulCommClass M N N := ⟨fun x y z ↦ by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩

end

section

variable {M N G H α β γ δ : Type*}

variable [SMul M α]

theorem comp.isScalarTower [SMul M β] [SMul α β] [IsScalarTower M α β] (g : N → M) : by
    haveI := comp α g; haveI := comp β g; exact IsScalarTower N α β where
  __ := comp α g
  __ := comp β g
  smul_assoc n := smul_assoc (g n)

end

section

variable {M N G H α β γ δ : Type*}

variable [SMul M α]

theorem comp.smulCommClass' [SMul β α] [SMulCommClass β M α] (g : N → M) :
    haveI := comp α g
    SMulCommClass β N α where
  __ := comp α g
  smul_comm _ n := smul_comm _ (g n)

end

section

variable {M N G H α β γ δ : Type*}

variable [SMul M α]

theorem comp.smulCommClass [SMul β α] [SMulCommClass M β α] (g : N → M) :
    haveI := comp α g
    SMulCommClass N β α where
  __ := comp α g
  smul_comm n := smul_comm (g n)

end

section

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem comp_smul_left (a₁ a₂ : M) : (a₁ • ·) ∘ (a₂ • ·) = (((a₁ * a₂) • ·) : α → α) := funext fun _ ↦ (mul_smul _ _ _).symm

end

section

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

variable [Group G] [MulAction G α] {g : G} {a b : α}

theorem inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a := by rw [smul_smul, inv_mul_cancel, one_smul]

end

section

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem isScalarTower_iff_smulCommClass_of_commMonoid (R₁ R : Type*)
    [Monoid R₁] [CommMonoid R] [MulAction R₁ R] :
    SMulCommClass R₁ R R ↔ IsScalarTower R₁ R R := ⟨fun _ ↦ IsScalarTower.of_commMonoid R₁ R, fun _ ↦ SMulCommClass.of_commMonoid R₁ R R⟩

end

section

variable {M N G H α β γ δ : Type*}

theorem mul_smul_one {M N} [MulOneClass N] [SMul M N] [SMulCommClass M N N] (x : M) (y : N) :
    y * x • (1 : N) = x • y := by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]

end

section

variable {M N G H α β γ δ : Type*}

theorem smul_div_assoc [DivInvMonoid β] [SMul α β] [IsScalarTower α β β] (r : α) (x y : β) :
    r • x / y = r • (x / y) := by simp [div_eq_mul_inv, smul_mul_assoc]

end

section

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

variable [Group G] [MulAction G α] {g : G} {a b : α}

variable [Group H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H]

theorem smul_inv (g : G) (a : H) : (g • a)⁻¹ = g⁻¹ • a⁻¹ := inv_eq_of_mul_eq_one_right <| by rw [smul_mul_smul_comm, mul_inv_cancel, mul_inv_cancel, one_smul]

end

section

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

variable [Group G] [MulAction G α] {g : G} {a b : α}

theorem smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a := by rw [smul_smul, mul_inv_cancel, one_smul]

end

section

variable {M N G H α β γ δ : Type*}

theorem smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsScalarTower α β β]
    [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c : α) (d : β) :
    (a • b) * (c • d) = (a * c) • (b * d) := by
  have : SMulCommClass β α β := .symm ..; exact smul_smul_smul_comm a b c d

end

section

variable {M N G H α β γ δ : Type*}

theorem smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ] [SMul α δ] [SMul γ δ]
    [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommClass β γ δ] (a : α) (b : β) (c : γ)
    (d : δ) : (a • b) • c • d = (a • c) • b • d := by rw [smul_assoc, smul_assoc, smul_comm b]

end

section

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

variable [Group G] [MulAction G α] {g : G} {a b : α}

variable [Group H] [MulAction G H] [SMulCommClass G H H] [IsScalarTower G H H]

theorem smul_zpow (g : G) (a : H) (n : ℤ) : (g • a) ^ n = g ^ n • a ^ n := by
  cases n <;> simp [smul_pow, smul_inv]

end
