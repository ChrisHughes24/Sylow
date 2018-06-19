import data.int.modeq data.int.basic data.nat.modeq data.fintype data.nat.prime data.nat.gcd

@[simp] lemma int.mod_mod (a b : ℤ) : a % b % b = a % b :=
by conv {to_rhs, rw [← int.mod_add_div a b, int.add_mul_mod_self_left]}

@[simp] lemma int.mod_neg_mod (a b : ℤ) : (-(a % b) % b) = (-a % b) :=
by conv {to_rhs, rw [← int.mod_add_div a b, neg_add, neg_mul_eq_mul_neg, int.add_mul_mod_self_left]}

open nat nat.modeq int

def Zmod := fin

namespace Zmod

--Copied from core, but marked as private in core
lemma mlt {n b : nat} : ∀ {a}, n > a → b % n < n
| 0     h := nat.mod_lt _ h
| (a+1) h :=
  have n > 0, from lt.trans (nat.zero_lt_succ _) h,
  nat.mod_lt _ this

class pos (n : ℕ) := (pos : 0 < n)

attribute [class] nat.prime

instance pos_of_prime (p : ℕ) [hp : nat.prime p] : pos p := ⟨hp.pos⟩

instance succ_pos (n : ℕ) : pos (nat.succ n) := ⟨succ_pos _⟩

def add_aux {n : ℕ} (a b : Zmod n) : Zmod n :=
⟨(a.1 + b.1) % n, mlt a.2⟩ 

def mul_aux {n : ℕ} (a b : Zmod n) : Zmod n :=
⟨(a.1 * b.1) % n, mlt a.2⟩

def neg_aux {n : ℕ} (a : Zmod n) : Zmod n :=
⟨nat_mod (-(a.1 : ℤ)) n, 
begin
  cases n with n,
  { exact (nat.not_lt_zero _ a.2).elim },
  { have h : (nat.succ n : ℤ) ≠ 0 := dec_trivial,
    rw [← int.coe_nat_lt, nat_mod, to_nat_of_nonneg (int.mod_nonneg _ h)],
    exact int.mod_lt _ h }
end⟩

instance (n : ℕ) : add_comm_semigroup (Zmod n) :=
{ add := add_aux,
  add_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq 
    (show ((a + b) % n + c) ≡ (a + (b + c) % n) [MOD n], 
    from calc ((a + b) % n + c) ≡ a + b + c [MOD n] : modeq_add (nat.mod_mod _ _) rfl
      ... ≡ a + (b + c) [MOD n] : by rw add_assoc
      ... ≡ (a + (b + c) % n) [MOD n] : modeq_add rfl (nat.mod_mod _ _).symm),
  add_comm := λ a b, fin.eq_of_veq (show (a.1 + b.1) % n = (b.1 + a.1) % n, by rw add_comm) }

instance (n : ℕ) : comm_semigroup (Zmod n) :=
{ mul := mul_aux,
  mul_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
    (calc ((a * b) % n * c) ≡ a * b * c [MOD n] : modeq_mul (nat.mod_mod _ _) rfl
      ... ≡ a * (b * c) [MOD n] : by rw mul_assoc
      ... ≡ a * (b * c % n) [MOD n] : modeq_mul rfl (nat.mod_mod _ _).symm),
  mul_comm := λ a b, fin.eq_of_veq (show (a.1 * b.1) % n = (b.1 * a.1) % n, by rw mul_comm) }

def one_aux (n : ℕ) [h0 : pos n] : Zmod n := ⟨1 % n, nat.mod_lt _ h0.pos⟩

lemma one_mul_aux (n : ℕ) [h0 : pos n] : ∀ a : Zmod n, one_aux n * a = a := 
λ ⟨a, ha⟩, fin.eq_of_veq (show (1 % n * a) % n = a, 
begin
  resetI,
  clear _fun_match,
  cases n with n,
  { simp },
  { cases n with n,
    { rw [nat.mod_self, zero_mul];
      exact (nat.eq_zero_of_le_zero (le_of_lt_succ ha)).symm },
    { have h : 1 < n + 2 := dec_trivial,
      have ha : a < succ (succ n) := ha,
      rw [nat.mod_eq_of_lt h, one_mul, nat.mod_eq_of_lt ha] } }
end)

lemma left_distrib_aux (n : ℕ) : ∀ a b c : Zmod n, a * (b + c) = a * b + a * c :=
λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, fin.eq_of_veq
(calc a * ((b + c) % n) ≡ a * (b + c) [MOD n] : modeq_mul rfl (nat.mod_mod _ _)
  ... ≡ a * b + a * c [MOD n] : by rw mul_add
  ... ≡ (a * b) % n + (a * c) % n [MOD n] : modeq_add (nat.mod_mod _ _).symm (nat.mod_mod _ _).symm)

instance (n : ℕ) : has_neg (Zmod n) := ⟨neg_aux⟩

instance (n : ℕ) : distrib (Zmod n) :=
{ left_distrib := left_distrib_aux n,
  right_distrib := λ a b c, by rw [mul_comm, left_distrib_aux, mul_comm _ b, mul_comm]; refl,
  ..Zmod.add_comm_semigroup n,
  ..Zmod.comm_semigroup n }

instance (n : ℕ) [h0 : pos n] : comm_ring (Zmod n) :=
{ zero := ⟨0, h0.pos⟩,
  zero_add := λ ⟨a, ha⟩, fin.eq_of_veq (show (0 + a) % n = a, by rw zero_add; exact nat.mod_eq_of_lt ha),
  add_zero := λ ⟨a, ha⟩, fin.eq_of_veq (nat.mod_eq_of_lt ha),
  neg := has_neg.neg,
  add_left_neg := 
    λ ⟨a, ha⟩, fin.eq_of_veq (show (((-a : ℤ) % n).to_nat + a) % n = 0,
      from int.coe_nat_inj
      begin
        have hn : (n : ℤ) ≠ 0 := (ne_of_lt (int.coe_nat_lt.2 h0.pos)).symm,
        rw [int.coe_nat_mod, int.coe_nat_add, to_nat_of_nonneg (int.mod_nonneg _ hn), add_comm],
        simp,
      end),
  one := ⟨1 % n, nat.mod_lt _ h0.pos⟩,
  one_mul := one_mul_aux n,
  mul_one := λ a, by rw mul_comm; exact one_mul_aux n a,
  ..Zmod.distrib n,
  ..Zmod.add_comm_semigroup n,
  ..Zmod.comm_semigroup n }

@[simp] lemma val_zero (n : ℕ) [pos n] : (0 : Zmod n).val = 0 := rfl

lemma cast_val {n : ℕ} [pos n] (a : ℕ) : (a : Zmod n).val = a % n :=
begin
  induction a with a ih,
  { rw [nat.zero_mod]; refl },
  { show ((a : Zmod n).val + 1 % n) % n = (a + 1) % n, 
    rw ih,
    exact nat.modeq.modeq_add (nat.mod_mod _ _) (nat.mod_mod _ _) }
end

lemma mk_eq_cast {a n : ℕ} (h : a < n) [pos n] : (⟨a, h⟩ : Zmod n) = (a : Zmod n) :=
fin.eq_of_veq (by rw [cast_val, nat.mod_eq_of_lt h])

@[simp] lemma cast_self_eq_zero (n : ℕ) [pos n] : (n : Zmod n) = 0 :=
fin.eq_of_veq (show (n : Zmod n).val = 0, by simp [cast_val])

lemma cast_val_of_lt {a n : ℕ} (h : a < n) [pos n] : (a : Zmod n).val = a :=
by rw [cast_val, nat.mod_eq_of_lt h]

@[simp] lemma cast_nat_mod (n : ℕ) [pos n] (a : ℕ) : ((a % n : ℕ) : Zmod n) = a :=
fin.eq_of_veq (show ((a % n : ℕ) : Zmod n).val = (a : Zmod n).val, by simp [cast_val])

instance Zmod_one.subsingleton : subsingleton (Zmod 1) := 
⟨λ a b, fin.eq_of_veq (by rw [eq_zero_of_le_zero (le_of_lt_succ a.2), 
  eq_zero_of_le_zero (le_of_lt_succ b.2)])⟩

instance Zmod_zero.subsingleton : subsingleton (Zmod 0) :=
⟨λ a, (nat.not_lt_zero _ a.2).elim⟩

instance (n : ℕ) : fintype (Zmod n) := fin.fintype _

lemma card_Zmod : ∀ n, fintype.card (Zmod n) = n := fintype.card_fin

end Zmod
