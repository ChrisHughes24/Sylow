import group_theory.order_of_element .Zmod algebra.pi_instances
open equiv fintype finset function
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

namespace finset

lemma filter_insert_of_pos [decidable_eq α] (s : finset α) {P : α → Prop} 
  [decidable_pred P] (a : α) (h : P a) : (insert a s).filter P = insert a (s.filter P) :=
ext.2 (λ x, by rw [mem_filter, mem_insert, mem_insert, mem_filter, eq_comm];
  exact ⟨λ h₁, by cases h₁.1; simp * at *, λ h₁, by cases h₁; simp * at *⟩)

lemma filter_insert_of_neg [decidable_eq α] (s : finset α) {P : α → Prop} 
  [decidable_pred P] (a : α) (h : ¬P a) : (insert a s).filter P = s.filter P :=
ext.2 (λ x, by rw [mem_filter, mem_insert, mem_filter, eq_comm];
  exact ⟨λ h₁, by cases h₁.1; simp * at *, by finish⟩)

lemma prod_const [comm_monoid β] (s : finset α) (b : β) 
  [decidable_eq α] : s.prod (λ x, b) = b ^ s.card :=
finset.induction_on s rfl (by simp [pow_add, mul_comm] {contextual := tt})

lemma sum_const [add_comm_monoid β] (s : finset α) (b : β) 
  [decidable_eq α] : s.sum (λ x, b) = add_monoid.smul s.card b :=
finset.induction_on s rfl (by simp [add_monoid.add_smul] {contextual := tt})

lemma card_pi {δ : α → Type*} [decidable_eq α]
  (s : finset α) (t : Π a, finset (δ a)) : (s.pi t).card = s.prod (λ a, card (t a)) :=
multiset.card_pi _ _

end finset

lemma nat.sum_mod [decidable_eq α] (s : finset α) (f : α → ℕ) (n : ℕ) : 
  s.sum f ≡ (s.filter (λ x, f x % n ≠ 0)).sum f [MOD n] :=
finset.induction_on s rfl begin 
  assume a s has ih,
  by_cases ha : f a % n ≠ 0,
  { rw [finset.sum_insert has, finset.filter_insert_of_pos s a ha, finset.sum_insert],
    exact nat.modeq.modeq_add rfl ih,
    { finish [finset.mem_filter] } },
  { rw [finset.sum_insert has, finset.filter_insert_of_neg s a ha, 
      ← zero_add (finset.sum (finset.filter _ _) _)],
    rw [ne.def, ← nat.zero_mod n] at ha,
    exact nat.modeq.modeq_add (not_not.1 ha) ih }  
end 

namespace fintype

instance quotient_fintype {α : Type*} [fintype α] (s : setoid α)
  [decidable_eq (quotient s)] : fintype (quotient s) :=
fintype.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

instance finset_fintype [fintype α] : fintype (finset α) :=
⟨finset.univ.powerset, λ x, finset.mem_powerset.2 (finset.subset_univ _)⟩

instance set.fintype (α : Type u) [fintype α] [decidable_eq α] : fintype (set α) :=
pi.fintype

def subtype_fintype [fintype α] (p : α → Prop) [decidable_pred p] : fintype {x // p x} :=
set_fintype _

lemma card_eq_one_iff [fintype α] : card α = 1 ↔ (∃ x : α, ∀ y : α, y = x) :=
by rw [← card_unit, card_eq]; exact
⟨λ ⟨a⟩, ⟨a.symm unit.star, λ y, a.bijective.1 (subsingleton.elim _ _)⟩, 
λ ⟨x, hx⟩, ⟨⟨λ _, unit.star, λ _, x, λ _, (hx _).trans (hx _).symm, 
    λ _, subsingleton.elim _ _⟩⟩⟩

lemma card_eq_zero_iff [fintype α] : card α = 0 ↔ (α → false) :=
⟨λ h a, have e : α ≃ empty := classical.choice (card_eq.1 (by simp [h])),
  (e a).elim, 
λ h, have e : α ≃ empty := ⟨λ a, (h a).elim, λ a, a.elim, λ a, (h a).elim, λ a, a.elim⟩, 
  by simp [card_congr e]⟩

lemma card_pos_iff [fintype α] : 0 < card α ↔ nonempty α :=
⟨λ h, classical.by_contradiction (λ h₁, 
  have card α = 0 := card_eq_zero_iff.2 (λ a, h₁ ⟨a⟩),
  lt_irrefl 0 $ by rwa this at h), 
λ ⟨a⟩, nat.pos_of_ne_zero (mt card_eq_zero_iff.1 (λ h, h a))⟩

lemma card_le_of_injective [fintype α] [fintype β] (f : α → β) 
  (hf : injective f) : card α ≤ card β :=
by haveI := classical.prop_decidable; exact
finset.card_le_card_of_inj_on f (λ _ _, finset.mem_univ _) (λ _ _ _ _ h, hf h)

lemma card_le_one_iff [fintype α] : card α ≤ 1 ↔ (∀ a b : α, a = b) :=
let n := card α in
have hn : n = card α := rfl,
match n, hn with
| 0 := λ ha, ⟨λ h, λ a, (card_eq_zero_iff.1 ha.symm a).elim, λ _, ha ▸ nat.le_succ _⟩
| 1 := λ ha, ⟨λ h, λ a b, let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm in
  by rw [hx a, hx b],
    λ _, ha ▸ le_refl _⟩
| (n+2) := λ ha, ⟨λ h, by rw ← ha at h; exact absurd h dec_trivial, 
  (λ h, card_unit ▸ card_le_of_injective (λ _, ())
    (λ _ _ _, h _ _))⟩
end

open finset

lemma card_pi {β : α → Type*} [fintype α] [decidable_eq α]
  [f : Π a, fintype (β a)] :
  card (Π a, β a) = univ.prod (λ a, card (β a)) :=
by letI f : fintype (Πa∈univ, β a) :=
  ⟨(univ.pi $ λa, univ), assume f, finset.mem_pi.2 $ assume a ha, mem_univ _⟩;
exact calc card (Π a, β a) = card (Π a ∈ univ, β a) : card_congr
  ⟨λ f a ha, f a, λ f a, f a (mem_univ a), λ _, rfl, λ _, rfl⟩ 
... = univ.prod (λ a, card (β a)) : finset.card_pi _ _

lemma card_fun [fintype α] [decidable_eq α] [fintype β] :
  card (α → β) = card β ^ card α :=
by rw [card_pi, prod_const, nat.pow_eq_pow]; refl

end fintype

namespace set

lemma card_eq_of_eq {s t : set α} [fintype s] [fintype t] (h : s = t) :
  card s = card t :=
by congr; assumption

lemma card_image_of_inj_on {s : set α} [fintype s]
  {f : α → β} [fintype (f '' s)] (H : ∀x∈s, ∀y∈s, f x = f y → x = y) :
  fintype.card (f '' s) = fintype.card s :=
by haveI := classical.prop_decidable; exact
calc fintype.card (f '' s) = (s.to_finset.image f).card : card_fintype_of_finset' _ (by simp)
... = s.to_finset.card : card_image_of_inj_on
    (λ x hx y hy hxy, H x (mem_to_finset.1 hx) y (mem_to_finset.1 hy) hxy)
... = card s : (card_fintype_of_finset' _ (λ a, mem_to_finset)).symm

lemma card_image_of_injective (s : set α) [fintype s]
  {f : α → β} [fintype (f '' s)] (H : injective f) : 
  fintype.card (f '' s) = fintype.card s :=
card_image_of_inj_on $ λ _ _ _ _ h, H h

lemma coe_to_finset' [decidable_eq α] (s : set α) [fintype s] : (↑s.to_finset : set α) = s :=
set.ext (by simp)

lemma ssubset_iff_subset_not_subset {s t : set α} : s ⊂ t ↔ s ⊆ t ∧ ¬ t ⊆ s :=
by split; simp [set.ssubset_def, ne.def, set.subset.antisymm_iff] {contextual := tt}

lemma coe_ssubset [decidable_eq α] {s t : finset α} : (↑s : set α) ⊂ ↑t ↔ s ⊂ t :=
show ↑s ⊆ ↑t ∧ ↑s ≠ ↑t ↔ s ⊆ t ∧ ¬t ⊆ s,
  by split; simp [ssubset_iff_subset_not_subset, set.subset.antisymm_iff] {contextual := tt}

lemma card_lt_card {s t : set α} [fintype s] [fintype t] (h : s ⊂ t) : card s < card t :=
begin
  haveI := classical.prop_decidable,
  rw [card_fintype_of_finset' _ (λ x, mem_to_finset), card_fintype_of_finset' _ (λ x, mem_to_finset)],
  rw [← coe_to_finset' s, ← coe_to_finset' t, coe_ssubset] at h,
  exact finset.card_lt_card h,
end

def equiv_univ (α : Type u) : α ≃ (set.univ : set α) :=
{ to_fun := λ a, ⟨a, mem_univ _⟩,
  inv_fun := λ a, a.1,
  left_inv := λ a, rfl,
  right_inv := λ ⟨a, ha⟩, rfl }

@[simp] lemma card_univ (α : Type u) [fintype α] [fintype.{u} (set.univ : set α)] : 
  fintype.card (set.univ : set α) = fintype.card α := 
eq.symm (card_congr (equiv_univ α))

lemma eq_of_card_eq_of_subset {s t : set α} [fintype s] [fintype t]
  (hcard : card s = card t) (hsub : s ⊆ t) : s = t :=
classical.by_contradiction (λ h, lt_irrefl (card t)
  (have card s < card t := set.card_lt_card ⟨hsub, h⟩,
    by rwa hcard at this))

end set

local attribute [instance, priority 0] 
  fintype.subtype_fintype set_fintype classical.prop_decidable

section should_be_in_group_theory

noncomputable instance [fintype G] (H : set G) [is_subgroup H] : 
fintype (left_cosets H) := fintype.quotient_fintype (left_rel H)

lemma card_eq_card_cosets_mul_card_subgroup [fintype G] (H : set G) [is_subgroup H] : 
  card G = card (left_cosets H) * card H :=
by rw ← card_prod;
  exact card_congr (is_subgroup.group_equiv_left_cosets_times_subgroup _)

lemma order_of_dvd_of_pow_eq_one [fintype G] {a : G} {n : ℕ} (h : a ^ n = 1) :
  order_of a ∣ n :=
by_contradiction
(λ h₁, nat.find_min _ (show n % order_of a < order_of a, 
  from nat.mod_lt _ (nat.pos_of_ne_zero (order_of_ne_zero _))) 
    ⟨mt nat.dvd_of_mod_eq_zero h₁, by rwa ← pow_eq_mod_order_of⟩)

lemma eq_one_of_order_of_eq_one [fintype G] {a : G} (h : order_of a = 1) : a = 1 :=
by conv { to_lhs, rw [← pow_one a, ← h, pow_order_of_eq_one] }

lemma order_eq_card_gpowers [fintype G] {a : G} : order_of a = card (gpowers a) :=
begin
  refine (finset.card_eq_of_bijective _ _ _ _).symm,
  { exact λn hn, ⟨gpow a n, ⟨n, rfl⟩⟩ },
  { exact assume ⟨_, i, rfl⟩ _,
    have pos: (0:int) < order_of a,
      from int.coe_nat_lt.mpr $ nat.pos_iff_ne_zero.mpr $ order_of_ne_zero a,
    have 0 ≤ i % (order_of a),
      from int.mod_nonneg _ $ ne_of_gt pos,
    ⟨int.to_nat (i % order_of a),
      by rw [← int.coe_nat_lt, int.to_nat_of_nonneg this];
        exact ⟨int.mod_lt_of_pos _ pos, subtype.eq gpow_eq_mod_order_of.symm⟩⟩ },
  { intros, exact finset.mem_univ _ },
  { exact assume i j hi hj eq, pow_injective_of_lt_order_of a hi hj $ by simpa using eq }
end

@[simp] lemma card_trivial [fintype (is_subgroup.trivial G)] :
  fintype.card (is_subgroup.trivial G) = 1 := fintype.card_eq_one_iff.2
  ⟨⟨(1 : G), by simp⟩, λ ⟨y, hy⟩, subtype.eq $ is_subgroup.mem_trivial.1 hy⟩

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

instance quotient.mk.is_group_hom (H : set G) [normal_subgroup H] : @is_group_hom G (left_cosets H) _ _ 
  quotient.mk := 
⟨λ _ _, rfl⟩

instance subtype.val.is_group_hom (H : set G) [is_subgroup H] : is_group_hom (subtype.val : H → G) :=
⟨λ _ _, rfl⟩

def normalizer (H : set G) : set G :=
{ g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H }

instance (H : set G) [is_subgroup H] : is_subgroup (normalizer H) :=
{ one_mem := by simp [normalizer],
  mul_mem := λ a b (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H)
    (hb : ∀ n, n ∈ H ↔ b * n * b⁻¹ ∈ H) n,
    by rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, ← hb],
  inv_mem := λ a (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) n,
    by rw [ha (a⁻¹ * n * a⁻¹⁻¹)];
    simp [mul_assoc] }

lemma subset_normalizer (H : set G) [is_subgroup H] : H ⊆ normalizer H :=
λ g hg n, by rw [is_subgroup.mul_mem_cancel_left _ ((is_subgroup.inv_mem_iff _).2 hg),
  is_subgroup.mul_mem_cancel_right _ hg]

instance (H : set G) [is_subgroup H] : normal_subgroup { x : normalizer H | ↑x ∈ H } :=
{ one_mem := show (1 : G) ∈ H, from is_submonoid.one_mem _,
  mul_mem := λ a b ha hb, show (a * b : G) ∈ H, from is_submonoid.mul_mem ha hb,
  inv_mem := λ a ha, show (a⁻¹ : G) ∈ H, from is_subgroup.inv_mem ha, 
  normal := λ a ha ⟨m, hm⟩, (hm a).1 ha }

lemma conj_inj_left {x : G} : injective (λ (n : G), x * n * x⁻¹) :=
λ a b h, (mul_left_inj x).1 $ (mul_right_inj (x⁻¹)).1 h

lemma mem_normalizer_fintype {H : set G} [fintype H] {x : G} :
  (∀ n, n ∈ H → x * n * x⁻¹ ∈ H) → x ∈ normalizer H :=
λ h n, ⟨h n, λ h₁,
have heq : (λ n, x * n * x⁻¹) '' H = H := set.eq_of_card_eq_of_subset
  (set.card_image_of_injective _ conj_inj_left) (λ n ⟨y, hy⟩, hy.2 ▸ h y hy.1),
have x * n * x⁻¹ ∈ (λ n, x * n * x⁻¹) '' H := heq.symm ▸ h₁,
let ⟨y, hy⟩ := this in conj_inj_left hy.2 ▸ hy.1⟩

noncomputable lemma preimage_quotient_mk_equiv_subgroup_times_set (H : set G) [is_subgroup H]
  (s : set (left_cosets H)) : quotient.mk ⁻¹' s ≃ (H × s) :=
have h : ∀ {x : left_cosets H} {a : G}, x ∈ s → a ∈ H → 
  ⟦quotient.out x * a⟧ = ⟦quotient.out x⟧ := λ x a hx ha,
      quotient.sound (show (quotient.out x * a)⁻¹ * quotient.out x ∈ H, 
      from (is_subgroup.inv_mem_iff _).1 $ 
        by rwa [mul_inv_rev, inv_inv, ← mul_assoc, inv_mul_self, one_mul]), 
{ to_fun := λ ⟨a, ha⟩, ⟨⟨(quotient.out ⟦a⟧)⁻¹ * a, 
    @quotient.exact _ (left_rel H) _ _ $ by simp⟩, ⟨⟦a⟧, ha⟩⟩,
  inv_fun := λ ⟨⟨a, ha⟩, ⟨x, hx⟩⟩, ⟨(quotient.out x) * a, 
    show _ ∈ s, by simpa [h hx ha]⟩,
  left_inv := λ ⟨a, ha⟩, by simp,
  right_inv := λ ⟨⟨a, ha⟩, ⟨x, hx⟩⟩, by simp [h hx ha] }

end should_be_in_group_theory

class is_group_action (f : G → α → α) : Prop :=
(one : ∀ a : α, f (1 : G) a = a)
(mul : ∀ (x y : G) (a : α), f (x * y) a = f x (f y a))

namespace group_action

variables (f : G → α → α) [is_group_action f] 

@[simp] lemma one_apply (a : α) : f 1 a = a := is_group_action.one f a

lemma mul_apply (x y : G) (a : α) : f (x * y) a = f x (f y a) := is_group_action.mul _ _ _ _

lemma bijective (g : G) : bijective (f g) :=
bijective_iff_has_inverse.2 ⟨f (g⁻¹), 
  λ a, by rw [← mul_apply f, inv_mul_self, one_apply f],
  λ a, by rw [← mul_apply f, mul_inv_self, one_apply f]⟩ 

def orbit (a : α) := set.range (λ x : G, f x a)

lemma mem_orbit_iff {f : G → α → α} [is_group_action f] {a b : α} :
  b ∈ orbit f a ↔ ∃ x : G, f x a = b :=
by finish [orbit]

@[simp] lemma mem_orbit (a : α) (x : G) :
  f x a ∈ orbit f a :=
⟨x, rfl⟩

@[simp] lemma mem_orbit_self (a : α) :
  a ∈ orbit f a :=
⟨1, show f 1 a = a, by simp [one_apply f]⟩

lemma orbit_eq {f : G → α → α} [is_group_action f] {a b : α} : a ∈ orbit f b → orbit f a = orbit f b :=
λ ⟨x, (hx : f x b = a)⟩, set.ext (λ c, ⟨λ ⟨y, (hy : f y a = c)⟩, ⟨y * x,
  show f (y * x) b = c, by rwa [mul_apply f, hx]⟩,
λ ⟨y, (hy : f y b = c)⟩, ⟨y * x⁻¹,
  show f (y * x⁻¹) a = c, by
    conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
      mul_apply f, hx]}⟩⟩)

instance orbit_fintype (a : α) [decidable_eq α] [fintype G] :
fintype (orbit f a) := set.fintype_range _

def stabilizer (a : α) : set G :=
{x : G | f x a = a}

lemma mem_stabilizer_iff {f : G → α → α} [is_group_action f] {a : α} {x : G} :
  x ∈ stabilizer f a ↔ f x a = a :=
iff.rfl

instance (a : α) : is_subgroup (stabilizer f a) :=
{ one_mem := one_apply _ _,
  mul_mem := λ x y (hx : f x a = a) (hy : f y a = a),
    show f (x * y) a = a, by rw mul_apply f; simp *,
  inv_mem := λ x (hx : f x a = a), show f x⁻¹ a = a,
    by rw [← hx, ← mul_apply f, inv_mul_self, one_apply f, hx] }

noncomputable lemma orbit_equiv_left_cosets (a : α) :
  orbit f a ≃ left_cosets (stabilizer f a) :=
by letI := left_rel (stabilizer f a); exact
equiv.symm (@equiv.of_bijective _ _ 
  (λ x : left_cosets (stabilizer f a), quotient.lift_on x 
    (λ x, (⟨f x a, mem_orbit _ _ _⟩ : orbit f a)) 
    (λ g h (H : _ = _), subtype.eq $ (group_action.bijective f (g⁻¹)).1
      $ show f g⁻¹ (f g a) = f g⁻¹ (f h a),
      by rw [← mul_apply f, ← mul_apply f, H, inv_mul_self, one_apply f])) 
⟨λ g h, quotient.induction_on₂ g h (λ g h H, quotient.sound $
  have H : f g a = f h a := subtype.mk.inj H, 
  show f (g⁻¹ * h) a = a,
  by rw [mul_apply f, ← H, ← mul_apply f, inv_mul_self, one_apply f]), 
  λ ⟨b, ⟨g, hgb⟩⟩, ⟨⟦g⟧, subtype.eq hgb⟩⟩)

def fixed_points : set α := {a : α | ∀ x, x ∈ stabilizer f a}

lemma mem_fixed_points {f : G → α → α} [is_group_action f] {a : α} :
  a ∈ fixed_points f ↔ ∀ x : G, f x a = a := iff.rfl

lemma mem_fixed_points' {f : G → α → α} [is_group_action f] {a : α} : a ∈ fixed_points f ↔
  (∀ b, b ∈ orbit f a → b = a) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, mem_stabilizer_iff.2 (h _ (mem_orbit _ _ _))⟩

lemma card_orbit_of_mem_fixed_points {f : G → α → α} [is_group_action f]  {a : α} [fintype (orbit f a)] : 
  a ∈ fixed_points f ↔ card (orbit f a) = 1 := 
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { exact λ h, ⟨⟨a, mem_orbit_self _ _⟩, λ ⟨b, ⟨x, hx⟩⟩, subtype.eq $ by simp [h x, hx.symm]⟩ },
  { assume h x,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    exact calc f x a = z : subtype.mk.inj (hz₁ ⟨f x a, mem_orbit _ _ _⟩)
      ... = a : (subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _ _⟩)).symm }
end

lemma card_modeq_card_fixed_points [fintype α] [fintype G] [fintype (fixed_points f)] 
  {p n : ℕ} (hp : nat.prime p) (h : card G = p ^ n) : card α ≡ card (fixed_points f) [MOD p] :=
have hcard : ∀ s : set α, card ↥{x : α | orbit f x = s} % p ≠ 0
    ↔ card ↥{x : α | orbit f x = s} = 1 :=
  λ s, ⟨λ hs, begin
    have h : ∃ y, orbit f y = s := by_contradiction (λ h, begin
      rw not_exists at h,
      have : {x | orbit f x = s} = ∅ := set.eq_empty_iff_forall_not_mem.2 h,
      rw [set.card_eq_of_eq this, set.empty_card', nat.zero_mod] at hs,
      contradiction
    end),
    cases h with y hy,
    have hseq : {x | orbit f x = s} = orbit f y := set.ext (λ z, 
      ⟨λ h : orbit f z = s, hy.symm ▸ h ▸ mem_orbit_self _ _, 
      λ h, show orbit f z = s, by rwa orbit_eq h⟩),
    rw [card_eq_card_cosets_mul_card_subgroup (stabilizer f y), 
      ← card_congr (orbit_equiv_left_cosets f y)] at h,
    have : ∃ k ≤ n, card (orbit f y) = p ^ k := (nat.dvd_prime_pow hp).1
      (h ▸ dvd_mul_right _ _),
    rcases this with ⟨k, hk₁, hk₂⟩,
    rw [set.card_eq_of_eq hseq, hk₂] at hs ⊢,
    have : ¬p ∣ p ^ k := mt nat.mod_eq_zero_of_dvd hs,
    cases k,
    { refl },
    { simpa [nat.pow_succ] using this }
  end,
  λ hs, hs.symm ▸ (nat.mod_eq_of_lt hp.gt_one).symm ▸ λ h, nat.no_confusion h⟩,
have h : (finset.univ.filter (λ a, card {x | orbit f x = a} % p ≠ 0)).sum 
  (λ a : set α, card {x | orbit f x = a}) = card (fixed_points f),
  from calc _ = (finset.univ.filter (λ a, card {x | orbit f x = a} % p ≠ 0)).sum 
    (λ a : set α, 1) : finset.sum_congr rfl (λ s hs, (hcard s).1 (finset.mem_filter.1 hs).2)
  ... = card {a : set α | card ↥{x : α | orbit f x = a} % p ≠ 0} :
  begin
    rw [finset.sum_const, nat.smul_eq_mul, mul_one],
    refine eq.symm (set.card_fintype_of_finset' _ _),
    simp [finset.mem_filter],
  end
  ... = card (fixed_points f) : fintype.card_congr 
    (@equiv.of_bijective _ _ 
      (show fixed_points f → {a : set α // card ↥{x : α | orbit f x = a} % p ≠ 0},
      from λ x, ⟨orbit f x.1, begin 
        rw [hcard, fintype.card_eq_one_iff],
        exact ⟨⟨x, rfl⟩, λ ⟨y, hy⟩, 
          have hy : y ∈ orbit f x := (show orbit f y = orbit f x, from hy) ▸ mem_orbit_self _ _,
          subtype.eq (mem_fixed_points'.1 x.2 _ hy)⟩
      end⟩) 
      ⟨λ x y hxy, 
        have hxy : orbit f x.1 = orbit f y.1 := subtype.mk.inj hxy,
        have hxo : x.1 ∈ orbit f y.1 := hxy ▸ mem_orbit_self _ _,
        subtype.eq (mem_fixed_points'.1 y.2 _ hxo), 
      λ ⟨s, hs⟩, begin
        rw [hcard, fintype.card_eq_one_iff] at hs,
        rcases hs with ⟨⟨x, hx₁⟩, hx₂⟩,
        exact ⟨⟨x, mem_fixed_points'.2 (λ y hy, 
          subtype.mk.inj (hx₂ ⟨y, by have := orbit_eq hy; simpa [this, hx₁] using hx₁⟩))⟩,
            by simpa using hx₁⟩
      end⟩).symm,
calc card α % p = finset.sum finset.univ (λ a : set α, card {x // orbit f x = a}) % p : 
  by rw [card_congr (equiv_fib (orbit f)), fintype.card_sigma] 
... = _ : nat.sum_mod _ _ _
... = fintype.card ↥(fixed_points f) % p : by rw ← h; congr

end group_action

namespace sylow
open group_action

def mk_vector_prod_eq_one (n : ℕ) [Zmod.pos n] (v : Zmod n → G) : Zmod (n+1) → G := 
λ m, if h : m.1 < n then v m.1 else ((list.range n).map (λ m : ℕ, v (m : Zmod n))).prod⁻¹

lemma mk_vector_prod_eq_one_injective {p : ℕ} [h0 : Zmod.pos p] : 
  injective (@mk_vector_prod_eq_one G _ p _) := 
λ x y hxy, funext (λ ⟨a, ha⟩, begin
  have : dite _ _ _ = dite _ _ _ := congr_fun hxy a,
  rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_of_lt ha), 
    dif_pos ha, dif_pos ha] at this,
  rwa Zmod.mk_eq_cast
end)

/-- set of elements of G^n such that the product of the 
  list of elements of the vector is one -/
def vectors_prod_eq_one (G : Type*) [group G] (n : ℕ) [Zmod.pos n] : set (Zmod n → G) := 
{v | ((list.range n).map (λ m : ℕ, v (↑m : Zmod n))).prod = 1 }

lemma mem_vectors_prod_eq_one_iff {n : ℕ} [Zmod.pos n] (v : Zmod (n + 1) → G) :
  v ∈ vectors_prod_eq_one G (n + 1) ↔ v ∈ mk_vector_prod_eq_one n '' (set.univ : set (Zmod n → G)) :=
have prod_lemma : ((list.range (n + 1)).map (λ m : ℕ, v (m : Zmod (n + 1)))).prod =
  list.prod (list.map (λ (m : ℕ), v ↑m) (list.range n)) * v ↑n :=
by rw [list.range_concat, list.map_append, list.prod_append,
  list.map_singleton, list.prod_cons, list.prod_nil, mul_one],
⟨λ h : list.prod (list.map (λ (m : ℕ), v ↑m) (list.range (n + 1))) = 1, 
  have h₁ : list.map (λ (m : ℕ), v ((m : Zmod n).val : Zmod (n+1))) (list.range n)
    = list.map (λ (m : ℕ), v m) (list.range n) := list.map_congr (λ m hm, 
  have hm' : m < n := list.mem_range.1 hm,  
    by simp [Zmod.cast_val, nat.mod_eq_of_lt hm']),
  ⟨λ m, v m.val, set.mem_univ _, funext (λ i, show dite _ _ _ = _, begin
    split_ifs,
    { refine congr_arg _ (fin.eq_of_veq _), 
      simp [Zmod.cast_val, nat.mod_eq_of_lt h_1, nat.mod_eq_of_lt (nat.lt_succ_of_lt h_1)] },
    { have hi : i = n := fin.eq_of_veq begin 
        rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_self _)],
        exact le_antisymm (nat.le_of_lt_succ i.2) (le_of_not_gt h_1),
      end,
      rw [h₁, hi, inv_eq_iff_mul_eq_one, ← prod_lemma, h] }
  end)⟩,
λ ⟨w, hw⟩, 
  have h : list.map (λ m : ℕ, w m) (list.range n) = list.map (λ m : ℕ, v m) (list.range n) :=
  list.map_congr (λ k hk, 
    have hk' : k < n := list.mem_range.1 hk,
    hw.2 ▸ (show _ = dite _ _ _, 
      by rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_of_lt hk'), dif_pos hk'])),
  begin
    show list.prod (list.map (λ (m : ℕ), v ↑m) (list.range (n + 1))) = 1,
    rw [prod_lemma, ← h, ← hw.2],
    show _ * dite _ _ _ = (1 : G),
    rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_self _), dif_neg (lt_irrefl _),
      mul_inv_self],
  end⟩

def rotate (α : Type v) (n : ℕ) (i : multiplicative (Zmod n)) (v : multiplicative (Zmod n) → α)
  (m : multiplicative (Zmod n)) := v (m * i) 

instance rotate.is_group_action (n : ℕ) [Zmod.pos n] :
  is_group_action (rotate α n) :=
{ mul := λ x y v, funext (λ i, show v (i * (x * y)) = v (i * x * y), by rw mul_assoc),
  one := λ v, funext (λ i, show v (i * 1) = v i, by rw mul_one) }

lemma fixed_points_rotate_eq_const {n : ℕ} [h0 : Zmod.pos n] {v : multiplicative (Zmod n) → G}
  (h : v ∈ fixed_points (rotate G n)) (i j : multiplicative (Zmod n)) : v i = v j :=
calc v i = v (j * i) : mul_comm i j ▸ (congr_fun ((mem_fixed_points'.1 h _) (mem_orbit (rotate G n) v j)) i).symm
... = v j : congr_fun ((mem_fixed_points'.1 h _) (mem_orbit (rotate G n) v i)) j

lemma map_succ_range : ∀ n : ℕ, list.range (nat.succ n) = 0 :: (list.range n).map nat.succ
| 0 := rfl
| (n+1) := by rw [list.range_concat, list.range_concat, list.map_append,
  ← list.cons_append, ← map_succ_range, list.range_concat, list.map_singleton]

open nat

lemma list.prod_const [monoid α] : ∀ {l : list α} {a : α}, (∀ b ∈ l, b = a) → l.prod = a ^ l.length
| [] := λ _ _, rfl
| (b::l) := λ a ha,
have h : ∀ b ∈ l, b = a := λ b hb, ha b (list.mem_cons_of_mem _ hb),
have hb : b = a := ha b (list.mem_cons_self _ _),
by simp [_root_.pow_add, list.prod_const h, hb]

lemma rotate_on_vectors_prod_eq_one {n : ℕ} [h0 : Zmod.pos n] {v : Zmod n → G}
  (hv : v ∈ vectors_prod_eq_one G n) (i : Zmod n) :
  (rotate G n) (i : Zmod n) v ∈ vectors_prod_eq_one G n :=
begin
  cases i with i hi,
  rw Zmod.mk_eq_cast,
  clear hi,
  induction i with i ih,
  { show list.prod (list.map (λ (m : ℕ), v (m + 0)) (list.range n)) = 1,
    simpa },
  { show list.prod (list.map (λ (m : ℕ), v (m + (i + 1))) (list.range n)) = 1,
    replace ih : list.prod (list.map (λ (m : ℕ), v (m + i)) (list.range n)) = 1 := ih,
    resetI,
    cases n,
    { simp [list.range, list.range_core] },
    { rw [list.range_concat, list.map_append, list.prod_append, list.map_singleton, 
        list.prod_cons, list.prod_nil, mul_one] at ⊢ ih,
      have h : list.map (λ m : ℕ, v (↑m + (i + 1))) (list.range n) =
        list.map (λ m : ℕ, v (m + i)) (list.map (λ m : ℕ, m + 1) (list.range n)),
      { simp [list.map_map, comp] },
      resetI,
      cases n,
      { refine eq.trans _ ih,
        simp [list.range, list.range_core]; congr },
      { have h : list.map (λ m : ℕ, v (↑m + (i + 1))) (list.range n) =
          list.map (λ m : ℕ, v (m + i)) (list.map succ (list.range n)),
        { simp [list.map_map, comp] },
        have h₁ : (succ n : Zmod (succ (succ n))) + (↑i + 1) = i,
        { rw [add_left_comm, ← nat.cast_one, ← nat.cast_add, Zmod.cast_self_eq_zero, add_zero] },
        have h₂ : (n : Zmod (succ (succ n))) + i + 1 = succ n + i := by simp [succ_eq_add_one],
        rw [map_succ_range, list.map_cons, list.prod_cons, ← h, nat.cast_zero, zero_add] at ih,
        have := eq_inv_mul_of_mul_eq ih,
        rw [list.range_concat, list.map_append, list.map_singleton, list.prod_append,
          list.prod_cons, list.prod_nil, mul_one, ← add_assoc, h₁, h₂, this],
        simp } } }
end

def rotate_vectors_prod_eq_one (G : Type u) [group G] (n : ℕ) [Zmod.pos n] (i : multiplicative (Zmod n)) 
  (v : vectors_prod_eq_one G n) : vectors_prod_eq_one G n := ⟨rotate _ n i v.1, rotate_on_vectors_prod_eq_one v.2 _⟩

instance (n : ℕ) [Zmod.pos n] : is_group_action (rotate_vectors_prod_eq_one G n) :=
{ one := λ ⟨a, ha⟩, subtype.eq (is_group_action.one (rotate G n) _),
  mul := λ x y ⟨a, ha⟩, subtype.eq (is_group_action.mul (rotate G n) _ _ _) }

lemma mem_fixed_points_rotate_vectors_prod_eq_one {n : ℕ} [Zmod.pos n]
  : ∀ {v : vectors_prod_eq_one G n}, v ∈ fixed_points (rotate_vectors_prod_eq_one G n) ↔ (v : Zmod n → G) ∈ fixed_points (rotate G n) :=
λ ⟨v, hv⟩, ⟨λ h x, subtype.mk.inj (h x), λ h x, subtype.eq (h x)⟩

lemma fixed_points_rotate_pow_n [fintype G] {n : ℕ} (hn : nat.prime (succ n))
  [h0 : Zmod.pos n] : ∀ {v : vectors_prod_eq_one G (succ n)}
  (hv : v ∈ fixed_points (rotate_vectors_prod_eq_one G (succ n))), (v : Zmod (succ n) → G) 0 ^ (n + 1) = 1 :=
λ ⟨v, hv₁⟩ hv,
let ⟨w, hw⟩ := (mem_vectors_prod_eq_one_iff _).1 hv₁ in
have hv' : (v : Zmod (succ n) → G) ∈ fixed_points (rotate G (succ n)) :=
  λ i, subtype.mk.inj (mem_stabilizer_iff.1 (hv i)),
begin
  have h₁ : dite _ _ _ = (v : Zmod (succ n) → G) _ := congr_fun hw.2 ⟨n, nat.lt_succ_self n⟩,
  rw dif_neg (lt_irrefl _) at h₁,
  have h₂ : ∀ b, b < n → w b = (v : Zmod (succ n) → G) b := λ b hb, begin
    have : dite _ _ _ = _ := congr_fun hw.2 b,
    rwa [Zmod.cast_val_of_lt (lt_succ_of_lt hb), dif_pos hb] at this,
  end,
  have hb : ∀ (b : G), b ∈ list.map (λ (m : ℕ), w ↑m) (list.range n) → b = w 0 := λ b hb,
    let ⟨i, hi⟩ := list.mem_map.1 hb in
    by rw [← hi.2, h₂ _ (list.mem_range.1 hi.1), fixed_points_rotate_eq_const hv' _ 1];
      exact (h₂ 0 h0.pos).symm,
  refine (@mul_left_inj _ _ (w 0 ^ (-n : ℤ)) _ _).1 _,
  rw [@list.prod_const _ _ _ (w 0) hb, list.length_map, list.length_range, ← gpow_coe_nat, ← gpow_neg] at h₁,
  conv { to_rhs, rw [h₁, fixed_points_rotate_eq_const hv' _ 1] },
  rw [← nat.cast_zero, h₂ 0 h0.pos, nat.cast_zero, subtype.coe_mk, ← gpow_coe_nat, ← _root_.gpow_add, int.coe_nat_add],
  simp, refl,
end

lemma one_mem_fixed_points_rotate [fintype G] {n : ℕ} [h0 : Zmod.pos n] :
  (1 : Zmod n → G) ∈ fixed_points (rotate G n) :=
mem_fixed_points'.2 (λ y hy, funext (λ j,
  let ⟨i, hi⟩ := mem_orbit_iff.1 hy in
  have hj : (1 : G) = y j := congr_fun hi j,
    hj ▸ rfl))

lemma one_mem_vectors_prod_eq_one (n : ℕ) [Zmod.pos n] : (1 : Zmod n → G) ∈ vectors_prod_eq_one G n :=
show list.prod (list.map (λ (m : ℕ), (1 : G)) (list.range n)) = 1,
from have h : ∀ b : G, b ∈ list.map (λ (m : ℕ), (1 : G)) (list.range n) → b = 1 :=
λ b hb, let ⟨_, h⟩ := list.mem_map.1 hb in h.2.symm,
by simp [list.prod_const h]

lemma exists_prime_order_of_dvd_card [fintype G] {p : ℕ} (hp : nat.prime p)
  (hdvd : p ∣ card G) : ∃ x : G, order_of x = p :=
let n := p - 1 in
have hn : p = n + 1 := nat.succ_sub hp.pos,
have hnp : nat.prime (n + 1) := hn ▸ hp,
have hn0 : Zmod.pos n := ⟨nat.lt_of_succ_lt_succ hnp.gt_one⟩,
have hlt : ¬(n : Zmod (n + 1)).val < n :=
  not_lt_of_ge (by rw [Zmod.cast_val, nat.mod_eq_of_lt (nat.lt_succ_self _)]; 
    exact le_refl _),
have hcard1 : card (vectors_prod_eq_one G (n + 1)) = card (Zmod n → G) := 
  by rw [← set.card_univ (Zmod n → G), set.ext (@mem_vectors_prod_eq_one_iff _ _ _ hn0), 
    set.card_image_of_injective _ mk_vector_prod_eq_one_injective],
have hcard : card (vectors_prod_eq_one G (n + 1)) = card G ^ n :=
  by conv { rw hcard1, to_rhs, rw ← card_fin n };
    exact fintype.card_fun,
have fintype (multiplicative (Zmod (succ n))) := fin.fintype _,
have Zmod.pos (succ n) := ⟨succ_pos _⟩,
have hZmod : @fintype.card (multiplicative (Zmod (succ n))) (fin.fintype _) = 
  (n+1) ^ 1 := (nat.pow_one (n + 1)).symm ▸ card_fin _,
by exactI
have hmodeq : _ = _ := @card_modeq_card_fixed_points _ _ _ (rotate_vectors_prod_eq_one G (succ n)) _ _ _ _ _ 1 hnp hZmod,
have hdvdcard : (n + 1) ∣ card (vectors_prod_eq_one G (n + 1)) :=
  calc (n + 1) = p : hn.symm
  ... ∣ card G ^ 1 : by rwa nat.pow_one
  ... ∣ card G ^ n : nat.pow_dvd_pow _ hn0.pos
  ... = card (vectors_prod_eq_one G (n + 1)) : hcard.symm,
have hdvdcard₂ : (n + 1) ∣ card (fixed_points (rotate_vectors_prod_eq_one G (succ n))) :=
  nat.dvd_of_mod_eq_zero (hmodeq ▸ (nat.mod_eq_zero_of_dvd hdvdcard)),
have hcard_pos : 0 < card (fixed_points (rotate_vectors_prod_eq_one G (succ n))) :=
  fintype.card_pos_iff.2 ⟨⟨⟨(1 : Zmod (succ n) → G), one_mem_vectors_prod_eq_one _⟩, 
    λ x, subtype.eq (one_mem_fixed_points_rotate x)⟩⟩,
have hle : 1 < card (fixed_points (rotate_vectors_prod_eq_one G (succ n))) :=
  calc 1 < n + 1 : hnp.gt_one
  ... ≤ _ : nat.le_of_dvd hcard_pos hdvdcard₂,
let ⟨⟨x, hx₁⟩, hx₂⟩ := classical.not_forall.1 (mt fintype.card_le_one_iff.2 (not_le_of_gt hle)) in
let ⟨⟨y, hy₁⟩, hy₂⟩ := classical.not_forall.1 hx₂ in
have hxy : (x : Zmod (succ n) → G) 0 ≠ 1 ∨ (y : Zmod (succ n) → G) 0 ≠ 1 := 
  or_iff_not_imp_left.2 
  (λ hx1 hy1, hy₂ $ subtype.eq $ subtype.eq $ funext $ λ i, 
  show (x : Zmod (succ n) → G) i = (y : Zmod (succ n) → G) i,
  by rw [fixed_points_rotate_eq_const ((mem_fixed_points_rotate_vectors_prod_eq_one).1 hx₁) _ (0 : Zmod (succ n)),
    fixed_points_rotate_eq_const ((mem_fixed_points_rotate_vectors_prod_eq_one).1 hy₁) _ (0 : Zmod (succ n)),
    not_not.1 hx1, hy1]),
have hxp : (x : Zmod (succ n) → G) 0 ^ (n + 1) = 1 := @fixed_points_rotate_pow_n _ _ _ _ hnp hn0 _ hx₁,
have hyp : (y : Zmod (succ n) → G) 0 ^ (n + 1) = 1 := @fixed_points_rotate_pow_n _ _ _ _ hnp hn0 _ hy₁,
begin
  rw hn,
  cases hxy with hx hy,
  { existsi (x : Zmod (succ n) → G) 0,
    exact or.resolve_left (hnp.2 _ (order_of_dvd_of_pow_eq_one hxp)) 
      (λ h, hx (eq_one_of_order_of_eq_one h)) },
  { existsi (y : Zmod (succ n) → G) 0,
    exact or.resolve_left (hnp.2 _ (order_of_dvd_of_pow_eq_one hyp))
      (λ h, hy (eq_one_of_order_of_eq_one h)) }
end

local attribute [instance] left_rel set_fintype
open is_subgroup is_submonoid is_group_hom

def mul_left_cosets (L₁ L₂ : set G) [is_subgroup L₂] [is_subgroup L₁]
  (x : L₂) (y : left_cosets L₁) : left_cosets L₁ :=
quotient.lift_on y (λ y, ⟦(x : G) * y⟧) 
  (λ a b (hab : _ ∈ L₁), quotient.sound 
    (show _ ∈ L₁, by rwa [mul_inv_rev, ← mul_assoc, mul_assoc (a⁻¹), inv_mul_self, mul_one]))
  
instance mul_left_cosets.is_group_action (L₁ L₂ : set G) [is_subgroup L₂] [is_subgroup L₁] : 
  is_group_action (mul_left_cosets L₁ L₂) :=
{ one := λ a, quotient.induction_on a (λ a, quotient.sound (show (1 : G) * a ≈ a, by simp)),
  mul := λ x y a, quotient.induction_on a (λ a, quotient.sound (by rw ← mul_assoc; refl)) }

lemma mem_fixed_points_mul_left_cosets_iff_mem_normalizer {H : set G} [is_subgroup H] [fintype H]
  {x : G} : ⟦x⟧ ∈ fixed_points (mul_left_cosets H H) ↔ x ∈ normalizer H := 
⟨λ hx, have ha : ∀ {y : left_cosets H}, y ∈ orbit (mul_left_cosets H H) ⟦x⟧ → y = ⟦x⟧ := λ _, 
    (mem_fixed_points'.1 hx _),
  (inv_mem_iff _).1 (mem_normalizer_fintype (λ n hn,
    have (n⁻¹ * x)⁻¹ * x ∈ H := quotient.exact (ha (mem_orbit (mul_left_cosets H H) _ 
      ⟨n⁻¹, inv_mem hn⟩)),
    by simpa only [mul_inv_rev, inv_inv] using this)),
λ (hx : ∀ (n : G), n ∈ H ↔ x * n * x⁻¹ ∈ H), 
mem_fixed_points'.2 $ λ y, quotient.induction_on y $ λ y hy, quotient.sound 
  (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy in 
  have hb₂ : (b * x)⁻¹ * y ∈ H := quotient.exact hb₂,
  (inv_mem_iff H).1 $ (hx _).2 $ (mul_mem_cancel_right H (inv_mem hb₁)).1
  $ by rw hx at hb₂;
    simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

lemma fixed_points_mul_left_cosets_equiv_cosets (H : set G) [is_subgroup H] [fintype H] :
  fixed_points (mul_left_cosets H H) ≃ left_cosets {x : normalizer H | ↑x ∈ H} :=
{ to_fun := λ a, quotient.hrec_on a.1 (λ a ha, @quotient.mk _
  (left_rel {x : normalizer H | ↑x ∈ H}) ⟨a, mem_fixed_points_mul_left_cosets_iff_mem_normalizer.1 ha⟩)
    (λ x y hxy, hfunext (by rw quotient.sound hxy)
      (λ hx hy _, heq_of_eq (@quotient.sound _ (left_rel {x : normalizer H | ↑x ∈ H})
        _ _ (by exact hxy)))) a.2,
  inv_fun := λ x, ⟨@quotient.lift_on _ _ (left_rel {x : normalizer H | ↑x ∈ H}) x
     (λ x, show (↥(fixed_points (mul_left_cosets H H)) : Type u),
       from ⟨⟦x⟧, mem_fixed_points_mul_left_cosets_iff_mem_normalizer.2 x.2⟩)
     (λ ⟨x, hx⟩ ⟨y, hy⟩ (hxy : x⁻¹ * y ∈ H), subtype.eq (quotient.sound hxy)), 
     (@quotient.induction_on _  (left_rel {x : normalizer H | ↑x ∈ H}) _ x
       (by intro x; cases x with x hx;
         exact mem_fixed_points_mul_left_cosets_iff_mem_normalizer.2 hx))⟩,
  left_inv := λ ⟨x, hx⟩, by revert hx;
    exact quotient.induction_on x (by intros; refl),
  right_inv := λ x, @quotient.induction_on _
    (left_rel {x : normalizer H | ↑x ∈ H}) _ x
      (by intro x; cases x; refl) }

lemma exists_subgroup_card_pow_prime [fintype G] {p : ℕ} : ∀ {n : ℕ} (hp : nat.prime p)
  (hdvd : p ^ n ∣ card G), ∃ H : set G, is_subgroup H ∧ card H = p ^ n
| 0 := λ _ _, ⟨trivial G, by apply_instance, by simp [-set.set_coe_eq_subtype]⟩
| (n+1) := λ hp hdvd,
let ⟨H, ⟨hH1, hH2⟩⟩ := exists_subgroup_card_pow_prime hp (dvd.trans (pow_dvd_pow _ (le_succ _)) hdvd) in
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
by exactI
have hcard : card (left_cosets H) = s * p :=
  (nat.mul_right_inj (show card H > 0, from fintype.card_pos_iff.2 ⟨⟨1, is_submonoid.one_mem H⟩⟩)).1
    (by rwa [← card_eq_card_cosets_mul_card_subgroup, hH2, hs, nat.pow_succ, mul_assoc, mul_comm p]),
have hm : s * p % p = card (left_cosets {x : normalizer H | ↑x ∈ H}) % p :=
  card_congr (fixed_points_mul_left_cosets_equiv_cosets H) ▸ hcard ▸ 
    card_modeq_card_fixed_points _ hp hH2,
have hm' : p ∣ card (left_cosets {x : normalizer H | ↑x ∈ H}) :=
  nat.dvd_of_mod_eq_zero
    (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm),
let ⟨x, hx⟩ := exists_prime_order_of_dvd_card hp hm' in
have hxcard : card (gpowers x) = p := by rwa ← order_eq_card_gpowers,
let S : set ↥(normalizer H) := set.preimage (@quotient.mk _
    (left_rel {x : ↥(normalizer H) | ↑x ∈ H}))
      (@gpowers (left_cosets {x : ↥(normalizer H) | ↑x ∈ H}) _ x) in
have is_subgroup S := @is_group_hom.preimage _
  (left_cosets {x : ↥(normalizer H) | ↑x ∈ H}) _ _ _ _ _ _,
have fS : fintype S := by apply_instance,
let hequiv : {x : ↥(normalizer H) | ↑x ∈ H} ≃ H :=
  { to_fun := λ ⟨x, hx⟩, ⟨x, hx⟩,
    inv_fun := λ ⟨x, hx⟩, ⟨⟨x, subset_normalizer _ hx⟩, hx⟩,
    left_inv := λ ⟨⟨_, _⟩, _⟩, rfl,
    right_inv := λ ⟨_, _⟩, rfl } in
⟨subtype.val '' S, by apply_instance,
by dsimp only [S];
  rw [set.card_image_of_injective _ subtype.val_injective, nat.pow_succ,
    @card_congr _ _ fS _ (preimage_quotient_mk_equiv_subgroup_times_set _ _),
    card_prod, hxcard, ← hH2, card_congr hequiv]⟩

def conjugate_set (x : G) (H : set G) : set G :=
(λ n, x⁻¹ * n * x) ⁻¹' H

lemma conjugate_set_eq_image (H : set G) (x : G) :
  conjugate_set x H = (λ n, x * n * x⁻¹) '' H :=
eq.symm (congr_fun (set.image_eq_preimage_of_inverse 
  (λ _, by simp [mul_assoc]) (λ _, by simp [mul_assoc])) _)

lemma conjugate_set_eq_preimage (H : set G) (x : G) :
  conjugate_set x H = (λ n, x⁻¹ * n * x) ⁻¹' H := rfl

instance conjugate_set.is_group_action : is_group_action (@conjugate_set G _) :=
{ one := λ H, by simp [conjugate_set_eq_image, set.image],
  mul := λ x y H, by simp [mul_inv_rev, mul_assoc, comp, conjugate_set_eq_preimage,
    set.preimage] }

@[simp] lemma conjugate_set_normal_subgroup (H : set G) [normal_subgroup H] (x : G) :
  conjugate_set x H = H :=
set.ext (λ n, ⟨λ h : _ ∈ H, by have := normal_subgroup.normal _ h x; simpa [mul_assoc] using this,
λ h, show _ ∈ H, by have := normal_subgroup.normal _ h (x⁻¹); by simpa using this⟩)

instance is_group_action.subgroup (H : set G) [is_subgroup H] (f : G → α → α) [is_group_action f] :
  is_group_action (λ x : H, f x) :=
{ one := λ a, is_group_action.one f a,
  mul := λ ⟨x, hx⟩ ⟨y, hy⟩ a, is_group_action.mul f x y a }

instance is_group_hom_conj (x : G) : is_group_hom (λ (n : G), x * n * x⁻¹) :=
⟨by simp [mul_assoc]⟩

instance is_subgroup_conj (x : G) (H : set G) [is_subgroup H] :
  is_subgroup (conjugate_set x H) :=
by rw conjugate_set_eq_image; apply_instance

/-- `dlogn p a` gives the maximum value of `n` such that `p ^ n ∣ a` -/
def dlogn (p : ℕ) : ℕ → ℕ
| 0     := 0
| (a+1) := if h : p > 1 then
  have (a + 1) / p < a + 1, from div_lt_self dec_trivial h,
    if p ∣ (a + 1) then dlogn ((a + 1) / p) + 1 else 0
  else 0

lemma dlogn_dvd {p : ℕ} : ∀ a, p > 1 → p ^ dlogn p a ∣ a
| 0     := λ _, dvd_zero _
| (a+1) := λ h,
have (a + 1) / p < a + 1, from div_lt_self dec_trivial h,
begin
  rw [dlogn, if_pos h],
  split_ifs with hd,
  { rw nat.pow_succ,
    conv { to_rhs, rw ← nat.div_mul_cancel hd },
    exact mul_dvd_mul (dlogn_dvd _ h) (dvd_refl _) },
  { simp }
end

lemma not_dvd_of_gt_dlogn {p : ℕ} : ∀ {a m}, a > 0 → p > 1 → m > dlogn p a → ¬p ^ m ∣ a
| 0     := λ m h, (lt_irrefl _ h).elim
| (a+1) := λ m h hp hm ,
have (a + 1) / p < a + 1, from div_lt_self dec_trivial hp,
begin
  rw [dlogn, if_pos hp] at hm,
  split_ifs at hm with hd,
  { have hmsub : succ (m - 1) = m := 
      succ_sub (show 1 ≤ m, from (lt_of_le_of_lt (nat.zero_le _) hm)) ▸ 
      (succ_sub_one m).symm,
    have := @not_dvd_of_gt_dlogn ((a + 1) / p) (m - 1)
      (pos_of_mul_pos_left (by rw nat.mul_div_cancel' hd; exact nat.succ_pos _) (nat.zero_le p))
      hp (lt_of_succ_lt_succ (hmsub.symm ▸ hm)),
    rwa [← nat.mul_dvd_mul_iff_right (lt_trans dec_trivial hp), nat.div_mul_cancel hd,
      ← nat.pow_succ, hmsub] at this },
  { assume h,
    exact hd (calc p = p ^ 1 : (nat.pow_one _).symm
      ... ∣ p ^ m : nat.pow_dvd_pow p hm
      ... ∣ a + 1 : h) }
end

lemma pow_dvd_of_dvd_mul {p : ℕ} : ∀ {m n k : ℕ} (hp : prime p) (hd : p ^ m ∣ n * k) (hk : ¬p ∣ k),
  p ^ m ∣ n
| 0     := by simp
| (m+1) := λ n k hp hd hk,
have hpnk : p ∣ n * k := calc p = p ^ 1 : by rw nat.pow_one
  ... ∣ p ^ (m + 1) : nat.pow_dvd_pow _ (succ_pos _)
  ... ∣ n * k : by assumption,
have hpn : p ∣ n := or.resolve_right (hp.dvd_mul.1 hpnk) hk,
have p ^ m ∣ (n / p) * k := dvd_of_mul_dvd_mul_right hp.pos $
  by rwa [mul_right_comm, nat.div_mul_cancel hpn, ← nat.pow_succ],
by rw [nat.pow_succ, ← nat.div_mul_cancel hpn];
  exact mul_dvd_mul_right (pow_dvd_of_dvd_mul hp this hk) _

lemma eq_dlogn_of_dvd_of_succ_not_dvd {a p n : ℕ} (hp : 1 < p) (h₁ : p ^ n ∣ a) (h₂ : ¬p ^ succ n ∣ a) : 
  n = dlogn p a :=
have ha : 0 < a := nat.pos_of_ne_zero (λ h, by simpa [h] using h₂),
le_antisymm (le_of_not_gt $ λ h, not_dvd_of_gt_dlogn ha hp h h₁)
  (le_of_not_gt $ λ h, h₂ $ calc p ^ succ n ∣ p ^ dlogn p a : nat.pow_dvd_pow _ h
    ... ∣ _ : dlogn_dvd _ hp)

lemma dlogn_eq_of_not_dvd {a b p  : ℕ} (hp : prime p) (hpb : ¬p ∣ b) : dlogn p a = dlogn p (a * b) :=
if ha : a = 0 then by simp [ha, dlogn] else
eq_dlogn_of_dvd_of_succ_not_dvd hp.gt_one (dvd.trans (dlogn_dvd _ hp.gt_one) (dvd_mul_right _ _))
  (λ h, not_dvd_of_gt_dlogn (nat.pos_of_ne_zero ha)
  hp.gt_one (lt_succ_self _) (pow_dvd_of_dvd_mul hp h hpb))

lemma not_dvd_div_dlogn {p a : ℕ} (ha : a > 0) (hp : p > 1) : ¬p ∣ a / (p ^ dlogn p a) :=
by rw [← nat.mul_dvd_mul_iff_left (nat.pos_pow_of_pos (dlogn p a) (lt_trans dec_trivial hp)),
    nat.mul_div_cancel' (dlogn_dvd _ hp), ← nat.pow_succ];
  exact not_dvd_of_gt_dlogn ha hp (lt_succ_self _)

class is_sylow [fintype G] (H : set G) {p : ℕ} (hp : prime p) extends is_subgroup H : Prop := 
(card_eq : card H = p ^ dlogn p (card G))

instance is_subgroup_in_subgroup (H K : set G) [is_subgroup H] [is_subgroup K] :
  is_subgroup {x : K | (x : G) ∈ H} :=
{ one_mem := show _ ∈ H, from one_mem _,
  mul_mem := λ x y hx hy, show x.1 * y.1 ∈ H, from mul_mem hx hy,
  inv_mem := λ x hx, show x.1⁻¹ ∈ H, from inv_mem hx }

lemma exists_sylow_subgroup (G : Type u) [group G] [fintype G] {p : ℕ} (hp : prime p) :
  ∃ H : set G, is_sylow H hp :=
let ⟨H, ⟨hH₁, hH₂⟩⟩ := exists_subgroup_card_pow_prime hp (dlogn_dvd (card G) hp.gt_one) in
by exactI ⟨H, by split; assumption⟩

lemma card_sylow [fintype G] (H : set G) [f : fintype H] {p : ℕ} (hp : prime p) [is_sylow H hp] :
  card H = p ^ dlogn p (card G) := 
by rw ← is_sylow.card_eq H hp; congr

lemma is_sylow_in_subgroup [fintype G] (H K : set G) {p : ℕ} (hp : prime p) [is_sylow H hp] (hsub : H ⊆ K)
  [is_subgroup K] : is_sylow {x : K | (x : G) ∈ H} hp :=
{ card_eq :=
  have h₁ : H = subtype.val '' {x : K | (x : G) ∈ H},
    from set.ext $ λ x, ⟨λ h, ⟨⟨x, hsub h⟩, ⟨h, rfl⟩⟩, λ ⟨y, hy⟩, hy.2 ▸ hy.1⟩,
  have h₂ : card K * (card G / card K) = card G := nat.mul_div_cancel' 
    ((card_eq_card_cosets_mul_card_subgroup K).symm ▸ dvd_mul_left _ _),
  have h₃ : ∀ {f : fintype {x : K | (x : G) ∈ H}}, @fintype.card {x : K | (x : G) ∈ H} f 
    = card H := λ f, by exactI
    calc @fintype.card {x : K | (x : G) ∈ H} f = card (subtype.val '' {x : K | (x : G) ∈ H}) :
      by exact (set.card_image_of_injective _ subtype.val_injective).symm
    ... = card H : set.card_eq_of_eq h₁.symm, 
  calc _ = _ : h₃ 
  ... = p ^ dlogn p (card G) : card_sylow H hp
  ... = p ^ dlogn p (card K) : congr_arg _ (h₂ ▸ eq.symm begin 
    refine dlogn_eq_of_not_dvd hp (λ h, _),
    have h₄ := mul_dvd_mul_left (card K) h,
    rw [h₂, card_eq_card_cosets_mul_card_subgroup {x : K | (x : G) ∈ H}, h₃, card_sylow H hp,
      mul_assoc, ← nat.pow_succ] at h₄,
    exact not_dvd_of_gt_dlogn (fintype.card_pos_iff.2 ⟨(1 : G)⟩) hp.gt_one (lt_succ_self _) 
      (dvd_of_mul_left_dvd h₄),
  end),
  ..sylow.is_subgroup_in_subgroup H K }

lemma sylow_conjugate [fintype G] {p : ℕ} (hp : prime p)
  (H K : set G) [is_sylow H hp] [is_sylow K hp] :
  ∃ g : G, H = conjugate_set g K :=
have hs : card (left_cosets K) = card G / (p ^ dlogn p (card G)) := 
  (nat.mul_right_inj (pos_pow_of_pos (dlogn p (card G)) hp.pos)).1
  $ by rw [← card_sylow K hp, ← card_eq_card_cosets_mul_card_subgroup, card_sylow K hp, 
    nat.div_mul_cancel (dlogn_dvd _ hp.gt_one)],
have hmodeq : card G / (p ^ dlogn p (card G)) ≡ card (fixed_points (mul_left_cosets K H)) [MOD p] := 
  hs ▸ card_modeq_card_fixed_points (mul_left_cosets K H) hp (card_sylow H hp),
have hfixed : 0 < card (fixed_points (mul_left_cosets K H)) := nat.pos_of_ne_zero 
  (λ h, (not_dvd_div_dlogn (fintype.card_pos_iff.2 ⟨(1 : G)⟩) hp.gt_one) 
    $ by rwa [h, nat.modeq.modeq_zero_iff] at hmodeq),
let ⟨⟨x, hx⟩⟩ := fintype.card_pos_iff.1 hfixed in
begin
  haveI : is_subgroup K := by apply_instance,
  revert hx,
  refine quotient.induction_on x
    (λ x hx, ⟨x, set.eq_of_card_eq_of_subset _ _⟩),
  { rw [conjugate_set_eq_image, set.card_image_of_injective _ conj_inj_left,
    card_sylow K hp, card_sylow H hp] },
  { assume y hy,
    have : (y⁻¹ * x)⁻¹ * x ∈ K := quotient.exact 
      (mem_fixed_points'.1 hx ⟦y⁻¹ * x⟧ ⟨⟨y⁻¹, inv_mem hy⟩, rfl⟩),
    simp [conjugate_set_eq_preimage, set.preimage, mul_inv_rev, *, mul_assoc] at * }
end

def conj_on_sylow [fintype G] {p : ℕ} (hp : nat.prime p)
  : Π (x : G) (H : {H : set G // is_sylow H hp}), {H : set G // is_sylow H hp} :=
λ x ⟨H, hH⟩, ⟨conjugate_set x H, by exactI
have h : is_subgroup (conjugate_set x H) := @sylow.is_subgroup_conj _ _ _ _ _,
{ card_eq := by exactI by
  rw [← card_sylow H hp, conjugate_set_eq_image, set.card_image_of_injective _ conj_inj_left],
  ..h }⟩

instance conj_on_sylow.is_group_action [fintype G] {p : ℕ} (hp : prime p) :
  is_group_action (@conj_on_sylow G _ _ _ hp) :=
{ one := λ ⟨H, hH⟩, by simp [conj_on_sylow, conjugate_set_eq_preimage, set.preimage],
  mul := λ x y ⟨H, hH⟩, by simp! [mul_inv_rev, mul_assoc, comp,
      conjugate_set_eq_image, (set.image_comp _ _ _).symm, conj_on_sylow] }

lemma card_sylow_dvd [fintype G] {p : ℕ} (hp : prime p) :
  card {H : set G // is_sylow H hp} ∣ card G :=
let ⟨H, hH⟩ := exists_sylow_subgroup G hp in
have h : orbit (conj_on_sylow hp) ⟨H, hH⟩ = set.univ :=
  set.eq_univ_iff_forall.2 (λ S, mem_orbit_iff.2 $
  let ⟨x, (hx : S.val = _)⟩ := @sylow_conjugate _ _ _ _ hp S.1 H S.2 hH in
  ⟨x, subtype.eq (hx.symm ▸ rfl)⟩),
have is_subgroup (stabilizer (conj_on_sylow hp) ⟨H, hH⟩) := group_action.is_subgroup _ _,
by exactI
have orbit_equiv : card (orbit (conj_on_sylow hp) ⟨H, hH⟩) =
  fintype.card (left_cosets (stabilizer (conj_on_sylow hp) ⟨H, hH⟩)) :=
   card_congr (orbit_equiv_left_cosets (conj_on_sylow hp) (⟨H, hH⟩ : {H : set G // is_sylow H hp})),
by exactI begin
  rw [h, ← card_congr (set.equiv_univ _)] at orbit_equiv,
  rw [orbit_equiv, card_congr (@group_equiv_left_cosets_times_subgroup _ _
    (stabilizer (conj_on_sylow hp) ⟨H, hH⟩) (by apply_instance)), card_prod],
  exact dvd_mul_right _ _
end

lemma card_sylow_modeq_one [fintype G] {p : ℕ} (hp : prime p) :
  card {H : set G // is_sylow H hp} ≡ 1 [MOD p] :=
let ⟨H, hH⟩ := exists_sylow_subgroup G hp in
by exactI
eq.trans
(card_modeq_card_fixed_points (λ x : H, conj_on_sylow hp (x : G)) hp (card_sylow H hp))
begin
  refine congr_fun (show (%) _ = (%) 1, 
    from congr_arg _ (fintype.card_eq_one_iff.2 _)) p,
  refine ⟨(⟨(⟨H, hH⟩ :  {H // is_sylow H hp}), λ ⟨x, hx⟩, subtype.eq $
    set.ext (λ i, by simp [conj_on_sylow, conjugate_set_eq_preimage, mul_mem_cancel_left _ hx,
      mul_mem_cancel_right _ (inv_mem hx)])⟩ :
        subtype (fixed_points (λ (x : ↥H), conj_on_sylow hp ↑x))), _⟩,
  refine λ L, subtype.eq (subtype.eq _),
  rcases L with ⟨⟨L, hL₁⟩, hL₂⟩,
  have Hsub : H ⊆ normalizer L,
  { assume x hx n,
    conv {to_rhs, rw ← subtype.mk.inj (hL₂ ⟨x, hx⟩)},
    simp [conjugate_set, mul_assoc] },
  suffices : ∀ x, x ∈ {x : normalizer L | (x : G) ∈ L} ↔ x ∈ {x : normalizer L | (x : G) ∈ H},
  { exact set.ext (λ x, ⟨λ h, (this ⟨x, subset_normalizer _ h⟩).1 h, λ h, (this ⟨x, Hsub h⟩).2 h⟩) },
  assume x,
  haveI := is_sylow_in_subgroup L (normalizer L) hp (subset_normalizer L),
  haveI := is_sylow_in_subgroup H (normalizer L) hp Hsub,
  cases sylow_conjugate hp {x : normalizer L | (x : G) ∈ H} {x | (x : G) ∈ L} with x hx,
  simp [hx]
end

end sylow