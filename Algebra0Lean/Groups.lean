import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Find
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Chapter II: Groups, first encounter

Selected results from Aluffi, *Algebra: Chapter 0*, §II.1 (Definition
of group).

This chapter defines its own `Group` structure from scratch, mirroring
the book's definition, rather than using Mathlib's `Group` typeclass —
so that the basic exercises (uniqueness of identity/inverse,
cancellation, ...) are genuine proof obligations. Later chapters
transition to Mathlib's `Group`.
-/

namespace Algebra0Lean.Groups

section DefinitionOfGroup

/-- **Definition II.1.1.** A group: a (nonempty, by virtue of `e`) type
`G` with an associative binary operation `op`, an identity `e` for
`op`, and inverses for every element. -/
structure Group (G : Type*) where
  op : G → G → G
  assoc : ∀ g h k : G, op (op g h) k = op g (op h k)
  e : G
  identity : ∀ g : G, op g e = g ∧ op e g = g
  inv : G → G
  inverse : ∀ g : G, op g (inv g) = e ∧ op (inv g) g = e

variable {G : Type*} (𝔾 : Group G)

/-- The group operation of `𝔾`, written infix as `g ⋆ h`. -/
local infixl:70 " ⋆ " => 𝔾.op

/-- `h` is an identity element for the group law of `𝔾`. -/
def IsIdentity (h : G) : Prop :=
  ∀ g : G, g ⋆ h = g ∧ h ⋆ g = g



/-- **Proposition II.1.2.** If `h` is an identity of `G`, then `h = e_G`. -/
theorem isIdentity_eq (h : G) (hh : IsIdentity 𝔾 h) : h = 𝔾.e := by
  have h1 := calc
   h = ( 𝔾.e ⋆ h ) := by exact (𝔾.identity h).2.symm
    _ = 𝔾.e := by exact (hh 𝔾.e).1
  exact h1


/-- `h` is an inverse of `g` with respect to the group law of `𝔾`. -/
def IsInverse (g h : G) : Prop :=
  g ⋆ h = 𝔾.e ∧ h ⋆ g = 𝔾.e

/-- **Proposition II.1.3.** The inverse of `g` is unique: if `h₁`, `h₂`
are both inverses of `g` in `G`, then `h₁ = h₂`. -/
theorem isInverse_unique (g h1 h2 : G)
    (hh1 : IsInverse 𝔾 g h1) (hh2 : IsInverse 𝔾 g h2) : h1 = h2 := by
  have η1 := by calc
    h1 = h1 ⋆ 𝔾.e := by exact (𝔾.identity h1).1.symm
     _ = h1 ⋆ (g ⋆ h2) := by rw [hh2.1]
     _ = (h1 ⋆  g) ⋆ h2 := by rw [𝔾.assoc]
     _ = 𝔾.e ⋆  h2 := by rw [hh1.2]
     _ = h2 := by exact (𝔾.identity h2).2     
  exact η1

end DefinitionOfGroup

section Cancellation

variable {G : Type*} (𝔾 : Group G)

local infixl:70 " ⋆ " => 𝔾.op

/-- **Proposition II.1.4** (Cancellation). Let `G` be a group. Then for
all `a, g, h ∈ G`, `ga = ha ⟹ g = h` and `ag = ah ⟹ g = h`. -/
theorem cancel_right (a g h : G) (heq : g ⋆ a = h ⋆ a) : g = h := by calc
    g = g ⋆ 𝔾.e := by exact (𝔾.identity g).1.symm
    _ = g ⋆ (a ⋆ 𝔾.inv a) := by rw [(𝔾.inverse a).1.symm]
    _ = (g ⋆ a) ⋆ (𝔾.inv a) := by rw [𝔾.assoc]
    _ = (h ⋆ a) ⋆ (𝔾.inv a) := by rw [heq]
    _ = h ⋆ (a ⋆ 𝔾.inv a) := by rw [𝔾.assoc]
    _ = h ⋆ 𝔾.e := by rw [(𝔾.inverse a).1]
    _ = h := by exact (𝔾.identity h).1

theorem cancel_left (a g h : G) (heq : a ⋆ g = a ⋆ h) : g = h := by
  have η1 := by calc
   g = 𝔾.e ⋆ g := by exact (𝔾.identity g).2.symm
   _ = (𝔾.inv a ⋆ a) ⋆ g := by rw [(𝔾.inverse a).2]
   _ = 𝔾.inv a ⋆ (a ⋆ g) := by rw [𝔾.assoc]
   _ = 𝔾.inv a ⋆ (a ⋆ h) := by rw [heq]
   _ = (𝔾.inv a ⋆ a) ⋆ h := by rw [𝔾.assoc]
   _ = 𝔾.e ⋆ h := by rw [(𝔾.inverse a).2]
   _ = h := by exact (𝔾.identity h).2
  exact η1

end Cancellation

section CommutativeGroups

variable {G : Type*} (𝔾 : Group G)

local infixl:70 " ⋆ " => 𝔾.op

/-- The group law of `𝔾` is commutative. -/
def IsCommutative : Prop :=
  ∀ g h : G, g ⋆ h = h ⋆ g

end CommutativeGroups

section Order

variable {G : Type*}

/-- The `n`-th power of `g` under the group law of `𝔾`. -/
def gpow (𝔾 : Group G) (g : G) : ℕ → G
  | 0 => 𝔾.e
  | n + 1 => 𝔾.op (gpow 𝔾 g n) g

/-- The `n`-th power of `g`, for `n : ℤ`, using `𝔾.inv` for negative
exponents. -/
def gzpow (𝔾 : Group G) (g : G) : ℤ → G
  | Int.ofNat n => gpow 𝔾 g n
  | Int.negSucc n => 𝔾.inv (gpow 𝔾 g (n + 1))

/-- Powers add: `g^(a+b) = g^a ⋆ g^b`. -/
theorem gpow_add (𝔾 : Group G) (g : G) (a b : ℕ) :
    gpow 𝔾 g (a + b) = 𝔾.op (gpow 𝔾 g a) (gpow 𝔾 g b) := by
  induction b with
  | zero => exact ((𝔾.identity (gpow 𝔾 g a)).1).symm
  | succ b ih =>
      show 𝔾.op (gpow 𝔾 g (a + b)) g = 𝔾.op (gpow 𝔾 g a) (𝔾.op (gpow 𝔾 g b) g)
      rw [ih, 𝔾.assoc]

/-- Powers add for integer exponents too: `g^(a+b) = g^a ⋆ g^b` for
`a b : ℤ` (the book's stated form of the law, right after introducing
powers). -/
theorem gzpow_add (𝔾 : Group G) (g : G) (a b : ℤ) :
    gzpow 𝔾 g (a + b) = 𝔾.op (gzpow 𝔾 g a) (gzpow 𝔾 g b) := by
  sorry

/-- Powers multiply: `g^(ab) = (g^a)^b`. -/
theorem gpow_mul (𝔾 : Group G) (g : G) (a b : ℕ) :
    gpow 𝔾 g (a * b) = gpow 𝔾 (gpow 𝔾 g a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      show gpow 𝔾 g (a * b + a) = 𝔾.op (gpow 𝔾 (gpow 𝔾 g a) b) (gpow 𝔾 g a)
      rw [gpow_add, ih]

/-- Every power of the identity is the identity. -/
theorem gpow_e (𝔾 : Group G) (n : ℕ) : gpow 𝔾 𝔾.e n = 𝔾.e := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show 𝔾.op (gpow 𝔾 𝔾.e n) 𝔾.e = 𝔾.e
      rw [ih]
      exact (𝔾.identity 𝔾.e).1

/-- If `h` commutes with `g`, it commutes with every power of `g`. -/
theorem gpow_op_comm (𝔾 : Group G) {g h : G} (hc : 𝔾.op g h = 𝔾.op h g) (n : ℕ) :
    𝔾.op (gpow 𝔾 g n) h = 𝔾.op h (gpow 𝔾 g n) := by
  induction n with
  | zero => exact ((𝔾.identity h).2).trans ((𝔾.identity h).1).symm
  | succ n ih =>
      show 𝔾.op (𝔾.op (gpow 𝔾 g n) g) h = 𝔾.op h (𝔾.op (gpow 𝔾 g n) g)
      rw [𝔾.assoc, hc, ← 𝔾.assoc, ih, 𝔾.assoc]

/-- For commuting `g`, `h`, powers distribute: `(gh)^n = g^n ⋆ h^n`. -/
theorem gpow_op_of_comm (𝔾 : Group G) {g h : G} (hc : 𝔾.op g h = 𝔾.op h g) (n : ℕ) :
    gpow 𝔾 (𝔾.op g h) n = 𝔾.op (gpow 𝔾 g n) (gpow 𝔾 h n) := by
  induction n with
  | zero => exact ((𝔾.identity 𝔾.e).1).symm
  | succ n ih =>
      show 𝔾.op (gpow 𝔾 (𝔾.op g h) n) (𝔾.op g h)
          = 𝔾.op (𝔾.op (gpow 𝔾 g n) g) (𝔾.op (gpow 𝔾 h n) h)
      calc 𝔾.op (gpow 𝔾 (𝔾.op g h) n) (𝔾.op g h)
          = 𝔾.op (𝔾.op (gpow 𝔾 g n) (gpow 𝔾 h n)) (𝔾.op g h) := by rw [ih]
        _ = 𝔾.op (gpow 𝔾 g n) (𝔾.op (𝔾.op (gpow 𝔾 h n) g) h) := by
              rw [𝔾.assoc, 𝔾.assoc]
        _ = 𝔾.op (gpow 𝔾 g n) (𝔾.op (𝔾.op g (gpow 𝔾 h n)) h) := by
              rw [gpow_op_comm 𝔾 hc.symm]
        _ = 𝔾.op (𝔾.op (gpow 𝔾 g n) g) (𝔾.op (gpow 𝔾 h n) h) := by
              rw [𝔾.assoc, 𝔾.assoc]

/-- The identity is its own inverse. -/
theorem inv_e (𝔾 : Group G) : 𝔾.inv 𝔾.e = 𝔾.e :=
  ((𝔾.identity (𝔾.inv 𝔾.e)).2).symm.trans (𝔾.inverse 𝔾.e).1

/-- `g⁻¹ = e` if and only if `g = e`. -/
theorem inv_eq_e_iff (𝔾 : Group G) (x : G) : 𝔾.inv x = 𝔾.e ↔ x = 𝔾.e := by
  constructor
  · intro h
    have h1 : 𝔾.op x (𝔾.inv x) = 𝔾.e := (𝔾.inverse x).1
    rw [h] at h1
    exact ((𝔾.identity x).1).symm.trans h1
  · rintro rfl
    exact inv_e 𝔾

/-- `g` has finite order if `g^n = e` for some positive `n`. -/
def HasFiniteOrder (𝔾 : Group G) (g : G) : Prop :=
  ∃ n : ℕ, 0 < n ∧ gpow 𝔾 g n = 𝔾.e

/-- **Definition II.1.5.** The order of `g`: the least positive `n`
with `g^n = e`, or `0` if `g` has infinite order (Aluffi's `|g| = ∞`). -/
noncomputable def order (𝔾 : Group G) (g : G) : ℕ := by
  classical exact if h : HasFiniteOrder 𝔾 g then Nat.find h else 0

/-- An element of finite order has positive order. -/
theorem order_pos (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g) :
    0 < order 𝔾 g := by
  classical
  unfold order
  rw [dif_pos hf]
  exact (Nat.find_spec hf).1

/-- `g^|g| = e` for an element of finite order. -/
theorem gpow_order (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g) :
    gpow 𝔾 g (order 𝔾 g) = 𝔾.e := by
  classical
  unfold order
  rw [dif_pos hf]
  exact (Nat.find_spec hf).2

/-- Minimality of the order: no smaller positive power of `g` is `e`. -/
theorem gpow_ne_e_of_lt_order (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g)
    {m : ℕ} (hm : 0 < m) (hlt : m < order 𝔾 g) : gpow 𝔾 g m ≠ 𝔾.e := by
  classical
  intro he
  unfold order at hlt
  rw [dif_pos hf] at hlt
  exact Nat.find_min hf hlt ⟨hm, he⟩

/-- An element of infinite order has order `0` (Aluffi's `|g| = ∞`). -/
theorem order_eq_zero_of_infinite (𝔾 : Group G) (g : G)
    (hf : ¬HasFiniteOrder 𝔾 g) : order 𝔾 g = 0 := by
  classical
  unfold order
  rw [dif_neg hf]

/-- An element of positive order has finite order. -/
theorem hasFiniteOrder_of_order_pos (𝔾 : Group G) (g : G)
    (h : 0 < order 𝔾 g) : HasFiniteOrder 𝔾 g := by
  by_contra hn
  rw [order_eq_zero_of_infinite 𝔾 g hn] at h
  exact Nat.lt_irrefl 0 h

/-- **Lemma II.1.5.** If `g^n = e` for some positive integer `n`, then
`|g|` is a divisor of `n`. -/
theorem order_dvd_of_pow_eq_e (𝔾 : Group G) (g : G) (n : ℕ) (hn : 0 < n)
    (he : gpow 𝔾 g n = 𝔾.e) : order 𝔾 g ∣ n := by
  have hf : HasFiniteOrder 𝔾 g := ⟨n, hn, he⟩
  have hpos : 0 < order 𝔾 g := order_pos 𝔾 g hf
  -- Division algorithm: `n = |g| * (n / |g|) + r` with `r = n % |g| < |g|`,
  -- so `g^r = e`.
  have hr : gpow 𝔾 g (n % order 𝔾 g) = 𝔾.e := by
    have h1 : order 𝔾 g * (n / order 𝔾 g) + n % order 𝔾 g = n :=
      Nat.div_add_mod n (order 𝔾 g)
    have h2 : gpow 𝔾 g (order 𝔾 g * (n / order 𝔾 g)) = 𝔾.e := by
      rw [gpow_mul, gpow_order 𝔾 g hf, gpow_e]
    calc gpow 𝔾 g (n % order 𝔾 g)
        = 𝔾.op 𝔾.e (gpow 𝔾 g (n % order 𝔾 g)) := ((𝔾.identity _).2).symm
      _ = 𝔾.op (gpow 𝔾 g (order 𝔾 g * (n / order 𝔾 g)))
            (gpow 𝔾 g (n % order 𝔾 g)) := by rw [h2]
      _ = gpow 𝔾 g (order 𝔾 g * (n / order 𝔾 g) + n % order 𝔾 g) :=
            (gpow_add 𝔾 g _ _).symm
      _ = gpow 𝔾 g n := by rw [h1]
      _ = 𝔾.e := he
  -- Minimality of the order forces the remainder to vanish.
  by_contra hnd
  have hr0 : 0 < n % order 𝔾 g :=
    Nat.pos_of_ne_zero fun h0 ↦ hnd (Nat.dvd_of_mod_eq_zero h0)
  exact gpow_ne_e_of_lt_order 𝔾 g hf hr0 (Nat.mod_lt n hpos) hr

/-- Restatement of Lemma II.1.5 as an equivalence, for natural exponents:
`g^n = e` if and only if `|g|` divides `n`. -/
theorem gpow_eq_e_iff_order_dvd (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g)
    (n : ℕ) : gpow 𝔾 g n = 𝔾.e ↔ order 𝔾 g ∣ n := by
  constructor
  · intro he
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Dvd.intro 0 rfl
    · exact order_dvd_of_pow_eq_e 𝔾 g n hn he
  · rintro ⟨k, rfl⟩
    rw [gpow_mul, gpow_order 𝔾 g hf, gpow_e]

/-- **Corollary II.1.6.** Let `g` be an element of finite order, and
let `N : ℤ`. Then `g^N = e ↔ N` is a multiple of `|g|`. -/
theorem gzpow_eq_e_iff_dvd_order (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g)
    (N : ℤ) : gzpow 𝔾 g N = 𝔾.e ↔ (order 𝔾 g : ℤ) ∣ N := by
  cases N with
  | ofNat n =>
      show gpow 𝔾 g n = 𝔾.e ↔ _
      rw [gpow_eq_e_iff_order_dvd 𝔾 g hf]
      exact Int.natCast_dvd_natCast.symm
  | negSucc n =>
      show 𝔾.inv (gpow 𝔾 g (n + 1)) = 𝔾.e ↔ _
      rw [inv_eq_e_iff, gpow_eq_e_iff_order_dvd 𝔾 g hf, ← Int.dvd_natAbs]
      exact Int.natCast_dvd_natCast.symm

/-- **Definition.** If `G` is finite as a set, its order `|G|` is the
number of its elements; `0` if `G` is infinite (Aluffi's `|G| = ∞`). -/
noncomputable def groupOrder : ℕ := Nat.card G

/-- **Proposition II.1.7.** Let `g` be an element of finite order.
Then `g^m` has finite order for all `m ≥ 0`, and
`|g^m| = lcm(m, |g|) / m = |g| / gcd(m, |g|)`.

The `lcm` form requires `0 < m`: for `m = 0` we have `|g^0| = |e| = 1`
while `lcm(0, |g|) / 0 = 0` in `ℕ` (Aluffi's second expression
`|g| / gcd(m, |g|)` does cover `m = 0`). -/
theorem order_gpow (𝔾 : Group G) (g : G) (hf : HasFiniteOrder 𝔾 g) (m : ℕ)
    (hm : 0 < m) :
    order 𝔾 (gpow 𝔾 g m) = Nat.lcm m (order 𝔾 g) / m := by
  have hgpos : 0 < order 𝔾 g := order_pos 𝔾 g hf
  -- `g^m` has finite order, since `(g^m)^|g| = (g^|g|)^m = e`.
  have hfm : HasFiniteOrder 𝔾 (gpow 𝔾 g m) := by
    refine ⟨order 𝔾 g, hgpos, ?_⟩
    rw [← gpow_mul, Nat.mul_comm, gpow_mul, gpow_order 𝔾 g hf, gpow_e]
  -- `(g^m)^d = e` exactly when `|g| ∣ m * d` (Lemma II.1.5).
  have key : ∀ d : ℕ, gpow 𝔾 (gpow 𝔾 g m) d = 𝔾.e ↔ order 𝔾 g ∣ m * d := by
    intro d
    rw [← gpow_mul, gpow_eq_e_iff_order_dvd 𝔾 g hf]
  -- Hence `m * |g^m|` is the least common multiple of `m` and `|g|`.
  have h1 : Nat.lcm m (order 𝔾 g) ∣ m * order 𝔾 (gpow 𝔾 g m) :=
    Nat.lcm_dvd (Dvd.intro _ rfl) ((key _).1 (gpow_order 𝔾 _ hfm))
  have h2 : m * order 𝔾 (gpow 𝔾 g m) ∣ Nat.lcm m (order 𝔾 g) := by
    have hmL : m ∣ Nat.lcm m (order 𝔾 g) := Nat.dvd_lcm_left _ _
    have hL : m * (Nat.lcm m (order 𝔾 g) / m) = Nat.lcm m (order 𝔾 g) :=
      Nat.mul_div_cancel' hmL
    have hLpos : 0 < Nat.lcm m (order 𝔾 g) :=
      Nat.pos_of_ne_zero (Nat.lcm_ne_zero hm.ne' hgpos.ne')
    have hquotpos : 0 < Nat.lcm m (order 𝔾 g) / m :=
      Nat.div_pos (Nat.le_of_dvd hLpos hmL) hm
    have hDe : gpow 𝔾 (gpow 𝔾 g m) (Nat.lcm m (order 𝔾 g) / m) = 𝔾.e := by
      rw [key, hL]
      exact Nat.dvd_lcm_right _ _
    calc m * order 𝔾 (gpow 𝔾 g m)
        ∣ m * (Nat.lcm m (order 𝔾 g) / m) :=
          Nat.mul_dvd_mul_left m (order_dvd_of_pow_eq_e 𝔾 _ _ hquotpos hDe)
      _ = Nat.lcm m (order 𝔾 g) := hL
  have hmD : m * order 𝔾 (gpow 𝔾 g m) = Nat.lcm m (order 𝔾 g) :=
    Nat.dvd_antisymm h2 h1
  rw [← hmD, Nat.mul_div_cancel_left _ hm]

/-- **Proposition II.1.8.** If `g` and `h` commute, then `|gh|` divides
`lcm(|g|, |h|)`. -/
theorem order_op_dvd_lcm (𝔾 : Group G) (g h : G) (hcomm : 𝔾.op g h = 𝔾.op h g) :
    order 𝔾 (𝔾.op g h) ∣ Nat.lcm (order 𝔾 g) (order 𝔾 h) := by
  -- If `g` or `h` has infinite order the lcm is `0` and the claim is trivial.
  rcases Nat.eq_zero_or_pos (order 𝔾 g) with hg0 | hgpos
  · rw [hg0, Nat.lcm_zero_left]
    exact dvd_zero _
  rcases Nat.eq_zero_or_pos (order 𝔾 h) with hh0 | hhpos
  · rw [hh0, Nat.lcm_zero_right]
    exact dvd_zero _
  -- Otherwise `(gh)^lcm(|g|,|h|) = g^lcm ⋆ h^lcm = e ⋆ e = e`, and
  -- Lemma II.1.5 applies.
  have hfg := hasFiniteOrder_of_order_pos 𝔾 g hgpos
  have hfh := hasFiniteOrder_of_order_pos 𝔾 h hhpos
  have hLpos : 0 < Nat.lcm (order 𝔾 g) (order 𝔾 h) :=
    Nat.pos_of_ne_zero (Nat.lcm_ne_zero hgpos.ne' hhpos.ne')
  have hgh : gpow 𝔾 (𝔾.op g h) (Nat.lcm (order 𝔾 g) (order 𝔾 h)) = 𝔾.e := by
    rw [gpow_op_of_comm 𝔾 hcomm,
      (gpow_eq_e_iff_order_dvd 𝔾 g hfg _).2 (Nat.dvd_lcm_left _ _),
      (gpow_eq_e_iff_order_dvd 𝔾 h hfh _).2 (Nat.dvd_lcm_right _ _)]
    exact (𝔾.identity 𝔾.e).1
  exact order_dvd_of_pow_eq_e 𝔾 _ _ hLpos hgh

end Order

end Algebra0Lean.Groups
