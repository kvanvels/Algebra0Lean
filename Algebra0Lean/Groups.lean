import Algebra0Lean.Prelims
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Find
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Chapter II: Groups, first encounter

Selected results from Aluffi, *Algebra: Chapter 0*, §II.1 (Definition
of group), §II.2 (Examples of groups), §II.3 (The category Grp),
§II.4 (Group homomorphisms), §II.5 (Free groups), §II.6 (Subgroups),
and §II.7 (Quotient groups).

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

variable (𝔾 : Group G)

local infixl:70 " ⋆ " => 𝔾.op

/-- Powers add: `g^(a+b) = g^a ⋆ g^b`. -/
theorem gpow_add (g : G) (a b : ℕ) :
    gpow 𝔾 g (a + b) = gpow 𝔾 g a ⋆ gpow 𝔾 g b := by
  induction b with
  | zero => exact ((𝔾.identity (gpow 𝔾 g a)).1).symm
  | succ b ih =>
      show gpow 𝔾 g (a + b) ⋆ g = gpow 𝔾 g a ⋆ (gpow 𝔾 g b ⋆ g)
      rw [ih, 𝔾.assoc]

/-- Powers add for integer exponents too: `g^(a+b) = g^a ⋆ g^b` for
`a b : ℤ` (the book's stated form of the law, right after introducing
powers). -/
theorem gzpow_add (g : G) (a b : ℤ) :
    gzpow 𝔾 g (a + b) = gzpow 𝔾 g a ⋆ gzpow 𝔾 g b := by
  sorry

/-- Powers multiply: `g^(ab) = (g^a)^b`. -/
theorem gpow_mul (g : G) (a b : ℕ) :
    gpow 𝔾 g (a * b) = gpow 𝔾 (gpow 𝔾 g a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      show gpow 𝔾 g (a * b + a) = gpow 𝔾 (gpow 𝔾 g a) b ⋆ gpow 𝔾 g a
      rw [gpow_add, ih]

/-- Every power of the identity is the identity. -/
theorem gpow_e (n : ℕ) : gpow 𝔾 𝔾.e n = 𝔾.e := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show gpow 𝔾 𝔾.e n ⋆ 𝔾.e = 𝔾.e
      rw [ih]
      exact (𝔾.identity 𝔾.e).1

/-- If `h` commutes with `g`, it commutes with every power of `g`. -/
theorem gpow_op_comm {g h : G} (hc : g ⋆ h = h ⋆ g) (n : ℕ) :
    gpow 𝔾 g n ⋆ h = h ⋆ gpow 𝔾 g n := by
  induction n with
  | zero => exact ((𝔾.identity h).2).trans ((𝔾.identity h).1).symm
  | succ n ih =>
      show gpow 𝔾 g n ⋆ g ⋆ h = h ⋆ (gpow 𝔾 g n ⋆ g)
      rw [𝔾.assoc, hc, ← 𝔾.assoc, ih, 𝔾.assoc]

/-- For commuting `g`, `h`, powers distribute: `(gh)^n = g^n ⋆ h^n`. -/
theorem gpow_op_of_comm {g h : G} (hc : g ⋆ h = h ⋆ g) (n : ℕ) :
    gpow 𝔾 (g ⋆ h) n = gpow 𝔾 g n ⋆ gpow 𝔾 h n := by
  induction n with
  | zero => exact ((𝔾.identity 𝔾.e).1).symm
  | succ n ih =>
      show gpow 𝔾 (g ⋆ h) n ⋆ (g ⋆ h)
          = gpow 𝔾 g n ⋆ g ⋆ (gpow 𝔾 h n ⋆ h)
      calc gpow 𝔾 (g ⋆ h) n ⋆ (g ⋆ h)
          = gpow 𝔾 g n ⋆ gpow 𝔾 h n ⋆ (g ⋆ h) := by rw [ih]
        _ = gpow 𝔾 g n ⋆ (gpow 𝔾 h n ⋆ g ⋆ h) := by
              rw [𝔾.assoc, 𝔾.assoc]
        _ = gpow 𝔾 g n ⋆ (g ⋆ gpow 𝔾 h n ⋆ h) := by
              rw [gpow_op_comm 𝔾 hc.symm]
        _ = gpow 𝔾 g n ⋆ g ⋆ (gpow 𝔾 h n ⋆ h) := by
              rw [𝔾.assoc, 𝔾.assoc]

/-- The identity is its own inverse. -/
theorem inv_e : 𝔾.inv 𝔾.e = 𝔾.e :=
  ((𝔾.identity (𝔾.inv 𝔾.e)).2).symm.trans (𝔾.inverse 𝔾.e).1

/-- `g⁻¹ = e` if and only if `g = e`. -/
theorem inv_eq_e_iff (x : G) : 𝔾.inv x = 𝔾.e ↔ x = 𝔾.e := by
  constructor
  · intro h
    have h1 : x ⋆ 𝔾.inv x = 𝔾.e := (𝔾.inverse x).1
    rw [h] at h1
    exact ((𝔾.identity x).1).symm.trans h1
  · rintro rfl
    exact inv_e 𝔾

/-- `g` has finite order if `g^n = e` for some positive `n`. -/
def HasFiniteOrder (g : G) : Prop :=
  ∃ n : ℕ, 0 < n ∧ gpow 𝔾 g n = 𝔾.e

/-- **Definition II.1.5.** The order of `g`: the least positive `n`
with `g^n = e`, or `0` if `g` has infinite order (Aluffi's `|g| = ∞`). -/
noncomputable def order (g : G) : ℕ := by
  classical exact if h : HasFiniteOrder 𝔾 g then Nat.find h else 0

/-- An element of finite order has positive order. -/
theorem order_pos (g : G) (hf : HasFiniteOrder 𝔾 g) :
    0 < order 𝔾 g := by
  classical
  unfold order
  rw [dif_pos hf]
  exact (Nat.find_spec hf).1

/-- `g^|g| = e` for an element of finite order. -/
theorem gpow_order (g : G) (hf : HasFiniteOrder 𝔾 g) :
    gpow 𝔾 g (order 𝔾 g) = 𝔾.e := by
  classical
  unfold order
  rw [dif_pos hf]
  exact (Nat.find_spec hf).2

/-- Minimality of the order: no smaller positive power of `g` is `e`. -/
theorem gpow_ne_e_of_lt_order (g : G) (hf : HasFiniteOrder 𝔾 g)
    {m : ℕ} (hm : 0 < m) (hlt : m < order 𝔾 g) : gpow 𝔾 g m ≠ 𝔾.e := by
  classical
  intro he
  unfold order at hlt
  rw [dif_pos hf] at hlt
  exact Nat.find_min hf hlt ⟨hm, he⟩

/-- An element of infinite order has order `0` (Aluffi's `|g| = ∞`). -/
theorem order_eq_zero_of_infinite (g : G)
    (hf : ¬HasFiniteOrder 𝔾 g) : order 𝔾 g = 0 := by
  classical
  unfold order
  rw [dif_neg hf]

/-- An element of positive order has finite order. -/
theorem hasFiniteOrder_of_order_pos (g : G)
    (h : 0 < order 𝔾 g) : HasFiniteOrder 𝔾 g := by
  by_contra hn
  rw [order_eq_zero_of_infinite 𝔾 g hn] at h
  exact Nat.lt_irrefl 0 h

/-- **Lemma II.1.5.** If `g^n = e` for some positive integer `n`, then
`|g|` is a divisor of `n`. -/
theorem order_dvd_of_pow_eq_e (g : G) (n : ℕ) (hn : 0 < n)
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
        = 𝔾.e ⋆ gpow 𝔾 g (n % order 𝔾 g) := ((𝔾.identity _).2).symm
      _ = gpow 𝔾 g (order 𝔾 g * (n / order 𝔾 g))
            ⋆ gpow 𝔾 g (n % order 𝔾 g) := by rw [h2]
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
theorem gpow_eq_e_iff_order_dvd (g : G) (hf : HasFiniteOrder 𝔾 g)
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
theorem gzpow_eq_e_iff_dvd_order (g : G) (hf : HasFiniteOrder 𝔾 g)
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
theorem order_gpow (g : G) (hf : HasFiniteOrder 𝔾 g) (m : ℕ)
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
theorem order_op_dvd_lcm (g h : G) (hcomm : g ⋆ h = h ⋆ g) :
    order 𝔾 (g ⋆ h) ∣ Nat.lcm (order 𝔾 g) (order 𝔾 h) := by
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
  have hgh : gpow 𝔾 (g ⋆ h) (Nat.lcm (order 𝔾 g) (order 𝔾 h)) = 𝔾.e := by
    rw [gpow_op_of_comm 𝔾 hcomm,
      (gpow_eq_e_iff_order_dvd 𝔾 g hfg _).2 (Nat.dvd_lcm_left _ _),
      (gpow_eq_e_iff_order_dvd 𝔾 h hfh _).2 (Nat.dvd_lcm_right _ _)]
    exact (𝔾.identity 𝔾.e).1
  exact order_dvd_of_pow_eq_e 𝔾 _ _ hLpos hgh

end Order

section ExamplesOfGroups

open Algebra0Lean.Prelims

/-- **Definition (Symmetric group).** Let `A` be a set. The
**symmetric group**, or **group of permutations**, of `A` is the
group `S_A` of automorphisms of `A` in the category of types: its
elements are the bijections `A → A`, with composition as the group
law. -/
noncomputable def symmetricGroup (A : Type*) : Group (Category.Aut typeCategory A) where
  op f g := ⟨typeCategory.comp g.1 f.1, f.2.isIso_comp g.2⟩
  assoc := by sorry
  e := ⟨typeCategory.id A, typeCategory.isIso_id A⟩
  identity := by sorry
  inv f := ⟨f.2.inv, f.2.isIso_inv⟩
  inverse := by sorry

end ExamplesOfGroups

section CyclicGroupsAndModularArithmetic

/-- **Congruence modulo `n`.** For `a b : ℤ`, `a ≡ b (mod n)` iff `n`
divides `b - a`. -/
def congMod (n : ℕ) (a b : ℤ) : Prop := (n : ℤ) ∣ (b - a)

/-- Congruence modulo `n` is an equivalence relation. -/
theorem equivalence_congMod (n : ℕ) : Equivalence (congMod n) := by
  sorry

/-- **Lemma.** Congruence mod `n` is compatible with addition: if
`a ≡ a'` and `b ≡ b'` (mod `n`), then `a + b ≡ a' + b'` (mod `n`). This
is what makes `[a] + [b] := [a + b]` well-defined on `ℤ/nℤ`. -/
theorem congMod_add {n : ℕ} {a a' b b' : ℤ}
    (ha : congMod n a a') (hb : congMod n b b') :
    congMod n (a + b) (a' + b') := by
  rcases ha with ⟨k0,hk0⟩
  rcases hb with ⟨k1,hk1⟩
  use (k0 + k1)
  rw [mul_add,←hk0,←hk1]
  ring_nf

/-- The setoid of congruence classes mod `n` on `ℤ`. -/
def zmodSetoid (n : ℕ) : Setoid ℤ where
  r := congMod n
  iseqv := equivalence_congMod n

/-- **The cyclic group `ℤ/nℤ`.** The additive group of congruence
classes mod `n`, with `[a] + [b] := [a + b]` (well-defined by
`congMod_add`). -/
def zmodGroup (n : ℕ) : Group (Quotient (zmodSetoid n)) where
  op := by
    apply Quotient.lift₂ (fun a b => (Quotient.mk (zmodSetoid n) (a + b)))
    rintro a0 b0 a1 b1 ⟨ka, hka⟩ ⟨kb, hkb⟩
    apply Quotient.sound
    apply congMod_add ⟨ka, hka⟩ ⟨kb, hkb⟩

  assoc := by
    rintro g h k
    rcases Quotient.exists_rep g with ⟨g, rfl⟩
    rcases Quotient.exists_rep h with ⟨h, rfl⟩
    rcases Quotient.exists_rep k with ⟨k, rfl⟩
    simp only [Quotient.lift_mk]
    rw [add_assoc]

  e := Quotient.mk (zmodSetoid n) 0
  identity := by
    intro g
    rcases Quotient.exists_rep g with ⟨g, rfl⟩
    simp

  inv := by
    apply Quotient.lift (fun a => (Quotient.mk (zmodSetoid n) (-a)))
    rintro a b ⟨k, hk⟩
    apply Quotient.sound
    use -k
    rw [mul_neg, ← hk]
    ring_nf

  inverse := by
    intro g
    rcases Quotient.exists_rep g with ⟨g, rfl⟩
    simp only [Quotient.lift_mk, add_neg_cancel, neg_add_cancel, and_self]

/-- **Proposition.** The order of `[m]ₙ` in `ℤ/nℤ` is `1` if `n ∣ m`,
and more generally `|[m]ₙ| = n / gcd(m, n)`. -/
theorem order_class {n : ℕ} (hn : 0 < n) (m : ℤ) :
    order (zmodGroup n) (Quotient.mk (zmodSetoid n) m) = n / Int.gcd m (n : ℤ) := by
  sorry
  

/-- `g` **generates** `𝔾`: every element of `G` is some integer power
of `g`. -/
def Generates {G : Type*} (𝔾 : Group G) (g : G) : Prop :=
  ∀ x : G, ∃ k : ℤ, x = gzpow 𝔾 g k

/-- **Corollary.** The class `[m]ₙ` generates `ℤ/nℤ` if and only if
`gcd(m, n) = 1`. -/
theorem generates_iff_coprime {n : ℕ} (hn : 0 < n) (m : ℤ) :
    Generates (zmodGroup n) (Quotient.mk (zmodSetoid n) m) ↔ Int.gcd m (n : ℤ) = 1 := by
  sorry

/-- Congruence mod `n` is compatible with multiplication: if `a ≡ a'`
and `b ≡ b'` (mod `n`), then `a * b ≡ a' * b'` (mod `n`). This is what
makes `[a] * [b] := [a * b]` well-defined on `ℤ/nℤ`. -/
theorem congMod_mul {n : ℕ} {a a' b b' : ℤ}
    (ha : congMod n a a') (hb : congMod n b b') :
    congMod n (a * b) (a' * b') := by
  sorry

/-- Coprimality with `n` only depends on the congruence class mod `n`:
if `m ≡ m'` (mod `n`), then `gcd(m, n) = 1 ↔ gcd(m', n) = 1`. This is
what makes `(ℤ/nℤ)^*` a well-defined subset of `ℤ/nℤ`. -/
theorem gcd_eq_one_congMod {n : ℕ} {m m' : ℤ} (h : congMod n m m') :
    Int.gcd m (n : ℤ) = 1 ↔ Int.gcd m' (n : ℤ) = 1 := by
  sorry

/-- Multiplication of congruence classes mod `n`: `[a]ₙ * [b]ₙ := [a*b]ₙ`. -/
def zmodMul (n : ℕ) :
    Quotient (zmodSetoid n) → Quotient (zmodSetoid n) → Quotient (zmodSetoid n) :=
  Quotient.lift₂ (fun a b => Quotient.mk (zmodSetoid n) (a * b))
    (fun _ _ _ _ ha hb => Quotient.sound (congMod_mul ha hb))

/-- A class `[m]ₙ` is a **unit** if `m` is coprime to `n`. -/
def isUnitClass (n : ℕ) : Quotient (zmodSetoid n) → Prop :=
  Quotient.lift (fun m => Int.gcd m (n : ℤ) = 1)
    (fun _ _ h => propext (gcd_eq_one_congMod h))

/-- **The group of units `(ℤ/nℤ)^*`** (as a type): classes `[m]ₙ` with
`gcd(m, n) = 1`. -/
def zmodUnits (n : ℕ) : Type := {x : Quotient (zmodSetoid n) // isUnitClass n x}

/-- `(ℤ/nℤ)^*` is closed under multiplication: the product of two
classes coprime to `n` is again coprime to `n`. -/
theorem isUnitClass_mul {n : ℕ} {x y : Quotient (zmodSetoid n)}
    (hx : isUnitClass n x) (hy : isUnitClass n y) :
    isUnitClass n (zmodMul n x y) := by
  sorry

/-- **Proposition.** Multiplication makes `(ℤ/nℤ)^*` into a group. -/
def zmodUnitsGroup (n : ℕ) : Group (zmodUnits n) where
  op x y := ⟨zmodMul n x.1 y.1, isUnitClass_mul x.2 y.2⟩
  assoc := by sorry
  e := ⟨Quotient.mk (zmodSetoid n) 1, by sorry⟩
  identity := by sorry
  inv := by sorry
  inverse := by sorry

end CyclicGroupsAndModularArithmetic

section CategoryGrp

/-- A function `φ : G → H` between the underlying sets of two groups
is a **group homomorphism** if it preserves the group operation:
`φ(a ⋆ b) = φ(a) ⋆ φ(b)`. -/
def IsGroupHom {G H : Type*} (𝔾 : Group G) (ℍ : Group H) (φ : G → H) : Prop :=
  ∀ a b : G, φ (𝔾.op a b) = ℍ.op (φ a) (φ b)

/-- **Proposition.** A group homomorphism preserves the identity:
`φ(e_G) = e_H`. -/
theorem IsGroupHom.map_e {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) : φ 𝔾.e = ℍ.e := by
  sorry

/-- **Proposition** (second part). A group homomorphism preserves
inverses: `φ(g⁻¹) = φ(g)⁻¹`. -/
theorem IsGroupHom.map_inv {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) (g : G) : φ (𝔾.inv g) = ℍ.inv (φ g) := by
  sorry

open Algebra0Lean.Prelims

/-- The composite of two group homomorphisms is a group homomorphism. -/
theorem IsGroupHom.comp {G H K : Type*} {𝔾 : Group G} {ℍ : Group H} {𝕂 : Group K}
    {φ : G → H} {ψ : H → K} (hφ : IsGroupHom 𝔾 ℍ φ) (hψ : IsGroupHom ℍ 𝕂 ψ) :
    IsGroupHom 𝔾 𝕂 (ψ ∘ φ) := by
  sorry

/-- **Grp: Definition.** The category of groups: objects are groups
(as a type `G` together with a `Group G` structure), morphisms are
group homomorphisms. -/
def groupCategory.{w} : Category.{w + 1, w} where
  Obj := Σ G : Type w, Group G
  Hom X Y := {φ : X.1 → Y.1 // IsGroupHom X.2 Y.2 φ}
  id X := ⟨id, fun _ _ => rfl⟩
  comp g f := ⟨g.1 ∘ f.1, f.2.comp g.2⟩
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **The trivial group.** The unique group structure on a
one-element type. -/
def trivialGroup : Group PUnit where
  op _ _ := PUnit.unit
  assoc _ _ _ := by sorry
  e := PUnit.unit
  identity _ := by sorry
  inv _ := PUnit.unit
  inverse _ := by sorry

/-- **Proposition.** Trivial groups are both initial and final in
`Grp` (a "zero object"). -/
theorem isInitial_and_isFinal_trivialGroup :
    groupCategory.IsInitial (⟨PUnit, trivialGroup⟩ : groupCategory.Obj) ∧
      groupCategory.IsFinal (⟨PUnit, trivialGroup⟩ : groupCategory.Obj) := by
  sorry

/-- **Direct product.** The componentwise group structure on `G × H`:
`(g₁, h₁) ⋆ (g₂, h₂) := (g₁ ⋆ g₂, h₁ ⋆ h₂)`. -/
def prodGroup {G H : Type*} (𝔾 : Group G) (ℍ : Group H) : Group (G × H) where
  op x y := (𝔾.op x.1 y.1, ℍ.op x.2 y.2)
  assoc := by sorry
  e := (𝔾.e, ℍ.e)
  identity := by sorry
  inv x := (𝔾.inv x.1, ℍ.inv x.2)
  inverse := by sorry

/-- The projection `G × H → G` is a group homomorphism. -/
theorem isGroupHom_fst {G H : Type*} (𝔾 : Group G) (ℍ : Group H) :
    IsGroupHom (prodGroup 𝔾 ℍ) 𝔾 Prod.fst := by
  sorry

/-- The projection `G × H → H` is a group homomorphism. -/
theorem isGroupHom_snd {G H : Type*} (𝔾 : Group G) (ℍ : Group H) :
    IsGroupHom (prodGroup 𝔾 ℍ) ℍ Prod.snd := by
  sorry

universe u

/-- **Proposition.** With the componentwise operation, `G × H` (with
its projections) is a product in `Grp`. -/
theorem isFinal_prodGroup {G H : Type u} (𝔾 : Group G) (ℍ : Group H) :
    (twoLegCategory groupCategory
        (⟨G, 𝔾⟩ : groupCategory.Obj) (⟨H, ℍ⟩ : groupCategory.Obj)).IsFinal
      ⟨⟨G × H, prodGroup 𝔾 ℍ⟩,
        ⟨Prod.fst, isGroupHom_fst 𝔾 ℍ⟩,
        ⟨Prod.snd, isGroupHom_snd 𝔾 ℍ⟩⟩ := by
  sorry

end CategoryGrp

section GroupHomomorphisms

universe u

/-- **Proposition.** Let `φ : G → H` be a group homomorphism, and let
`g ∈ G` be an element of finite order. Then `|φ(g)|` divides `|g|`. -/
theorem order_map_dvd {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) {g : G} (hg : HasFiniteOrder 𝔾 g) :
    order ℍ (φ g) ∣ order 𝔾 g := by
  sorry

/-- **Proposition.** A group homomorphism `φ : G → H` is an
isomorphism (in `Grp`) if and only if it is a bijection. -/
theorem groupCategory_isIso_iff_bijective {G H : Type u} {𝔾 : Group G} {ℍ : Group H}
    {φ : G → H} (hφ : IsGroupHom 𝔾 ℍ φ) :
    groupCategory.IsIso
        (⟨φ, hφ⟩ : groupCategory.Hom (⟨G, 𝔾⟩ : groupCategory.Obj) (⟨H, ℍ⟩ : groupCategory.Obj))
      ↔ Function.Bijective φ := by
  sorry

/-- **Definition.** Two groups `G`, `H` are **isomorphic** if there is
a bijective group homomorphism `G → H`. -/
def IsomorphicGroups {G H : Type*} (𝔾 : Group G) (ℍ : Group H) : Prop :=
  ∃ φ : G → H, IsGroupHom 𝔾 ℍ φ ∧ Function.Bijective φ

/-- **The additive group of integers.** -/
def intGroup : Group ℤ where
  op := (· + ·)
  assoc := by sorry
  e := 0
  identity := by sorry
  inv := Neg.neg
  inverse := by sorry

/-- **Definition.** A group `G` is **cyclic** if it is isomorphic to
`ℤ` or to `ℤ/nℤ` for some `n`. -/
def IsCyclicGroup {G : Type*} (𝔾 : Group G) : Prop :=
  IsomorphicGroups 𝔾 intGroup ∨ ∃ n : ℕ, IsomorphicGroups 𝔾 (zmodGroup n)

/-- **Proposition** (first part). An isomorphism preserves order:
`∀ g ∈ G, |φ(g)| = |g|`. -/
theorem order_eq_of_groupIso {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) (hbij : Function.Bijective φ) (g : G) :
    order ℍ (φ g) = order 𝔾 g := by
  sorry

/-- **Proposition** (second part). An isomorphism preserves
commutativity: `G` is commutative if and only if `H` is. -/
theorem isCommutative_iff_of_groupIso {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) (hbij : Function.Bijective φ) :
    IsCommutative 𝔾 ↔ IsCommutative ℍ := by
  sorry

/-- **Definition.** The type of group homomorphisms `G → H`. -/
def GroupHom {G H : Type*} (𝔾 : Group G) (ℍ : Group H) : Type _ :=
  {φ : G → H // IsGroupHom 𝔾 ℍ φ}

/-- **Proposition.** If `A` is an abelian group, then `Hom(G, A)`,
with pointwise operation, is itself an abelian group. -/
def homGroup {G H : Type*} (𝔾 : Group G) {ℍ : Group H} (hH : IsCommutative ℍ) :
    Group (GroupHom 𝔾 ℍ) where
  op f g := ⟨fun x => ℍ.op (f.1 x) (g.1 x), by sorry⟩
  assoc := by sorry
  e := ⟨fun _ => ℍ.e, by sorry⟩
  identity := by sorry
  inv f := ⟨fun x => ℍ.inv (f.1 x), by sorry⟩
  inverse := by sorry

theorem isCommutative_homGroup {G H : Type*} {𝔾 : Group G} {ℍ : Group H} (hH : IsCommutative ℍ) :
    IsCommutative (homGroup 𝔾 hH) := by
  sorry

end GroupHomomorphisms

section FreeGroups

/-- **Definition.** A group `F` together with a function `ι : S → F`
is the **free group on `S`** if for every group `H` and every
function `f : S → H`, there is a unique group homomorphism
`φ : F → H` with `φ ∘ ι = f`. -/
def IsFreeGroupOn {S F : Type*} (𝔽 : Group F) (ι : S → F) : Prop :=
  ∀ {H : Type*} (ℍ : Group H) (f : S → H), ∃! φ : F → H, IsGroupHom 𝔽 ℍ φ ∧ φ ∘ ι = f

/-- **Proposition.** The free group on `S`, if it exists, is unique
up to isomorphism: if `(F₁, ι₁)` and `(F₂, ι₂)` are both free on `S`,
then `F₁ ≅ F₂`. -/
theorem isomorphicGroups_of_isFreeGroupOn {S F₁ F₂ : Type*} {𝔽₁ : Group F₁} {𝔽₂ : Group F₂}
    {ι₁ : S → F₁} {ι₂ : S → F₂} (h₁ : IsFreeGroupOn 𝔽₁ ι₁) (h₂ : IsFreeGroupOn 𝔽₂ ι₂) :
    IsomorphicGroups 𝔽₁ 𝔽₂ := by
  sorry

/-- **Definition.** An abelian group `F` together with a function
`ι : S → F` is the **free abelian group on `S`** if for every abelian
group `H` and every function `f : S → H`, there is a unique group
homomorphism `φ : F → H` with `φ ∘ ι = f`. -/
def IsFreeAbelianGroupOn {S F : Type*} (𝔽 : Group F) (_hF : IsCommutative 𝔽) (ι : S → F) : Prop :=
  ∀ {H : Type*} (ℍ : Group H), IsCommutative ℍ →
    ∀ f : S → H, ∃! φ : F → H, IsGroupHom 𝔽 ℍ φ ∧ φ ∘ ι = f

/-- **Proposition.** The free abelian group on `S`, if it exists, is
unique up to isomorphism. -/
theorem isomorphicGroups_of_isFreeAbelianGroupOn {S F₁ F₂ : Type*} {𝔽₁ : Group F₁}
    {𝔽₂ : Group F₂} {hF₁ : IsCommutative 𝔽₁} {hF₂ : IsCommutative 𝔽₂} {ι₁ : S → F₁} {ι₂ : S → F₂}
    (h₁ : IsFreeAbelianGroupOn 𝔽₁ hF₁ ι₁) (h₂ : IsFreeAbelianGroupOn 𝔽₂ hF₂ ι₂) :
    IsomorphicGroups 𝔽₁ 𝔽₂ := by
  sorry

end FreeGroups

section Subgroups

/-- **Definition.** A subset `H` of `G` is a **subgroup** of `𝔾` if it
contains the identity and is closed under the operation and under
taking inverses. -/
def IsSubgroup {G : Type*} (𝔾 : Group G) (H : Set G) : Prop :=
  𝔾.e ∈ H ∧ (∀ a ∈ H, ∀ b ∈ H, 𝔾.op a b ∈ H) ∧ ∀ a ∈ H, 𝔾.inv a ∈ H

/-- **Definition.** The **kernel** of a group homomorphism `φ`. -/
def GroupHom.ker {G H : Type*} (ℍ : Group H) (φ : G → H) : Set G :=
  {g | φ g = ℍ.e}

/-- **Definition.** The **image** of a group homomorphism `φ`. -/
def GroupHom.image {G H : Type*} (φ : G → H) : Set H :=
  Set.range φ

/-- **Proposition.** The kernel of a group homomorphism is a subgroup
of the domain. -/
theorem isSubgroup_ker {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) : IsSubgroup 𝔾 (GroupHom.ker ℍ φ) := by
  sorry

/-- **Proposition.** The image of a group homomorphism is a subgroup
of the codomain. -/
theorem isSubgroup_image {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) : IsSubgroup ℍ (GroupHom.image φ) := by
  sorry

/-- **Proposition.** A group homomorphism is injective if and only if
its kernel is trivial. -/
theorem injective_iff_ker_eq_singleton_e {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) : Function.Injective φ ↔ GroupHom.ker ℍ φ = {𝔾.e} := by
  sorry

/-- **Definition.** The **subgroup generated by** a subset `S` of `G`:
the intersection of all subgroups of `G` containing `S`. -/
def generatedSubgroup {G : Type*} (𝔾 : Group G) (S : Set G) : Set G :=
  ⋂₀ {H | IsSubgroup 𝔾 H ∧ S ⊆ H}

/-- **Proposition.** `generatedSubgroup 𝔾 S` is itself a subgroup. -/
theorem isSubgroup_generatedSubgroup {G : Type*} (𝔾 : Group G) (S : Set G) :
    IsSubgroup 𝔾 (generatedSubgroup 𝔾 S) := by
  sorry

/-- **Proposition.** `S` is contained in the subgroup it generates. -/
theorem subset_generatedSubgroup {G : Type*} (𝔾 : Group G) (S : Set G) :
    S ⊆ generatedSubgroup 𝔾 S := by
  sorry

/-- **Proposition.** `generatedSubgroup 𝔾 S` is the smallest subgroup
containing `S`: it is contained in every subgroup `H` with `S ⊆ H`. -/
theorem generatedSubgroup_subset {G : Type*} (𝔾 : Group G) (S H : Set G) (hH : IsSubgroup 𝔾 H)
    (hSH : S ⊆ H) : generatedSubgroup 𝔾 S ⊆ H := by
  sorry

/-- **Definition.** A subgroup `H` of `𝔾`, with its own group
structure: the operation, identity, and inverse are those of `𝔾`,
restricted to `H`. -/
def IsSubgroup.toGroup {G : Type*} {𝔾 : Group G} {H : Set G} (hH : IsSubgroup 𝔾 H) :
    Group {x // x ∈ H} where
  op a b := ⟨𝔾.op a.1 b.1, hH.2.1 a.1 a.2 b.1 b.2⟩
  assoc := by sorry
  e := ⟨𝔾.e, hH.1⟩
  identity := by sorry
  inv a := ⟨𝔾.inv a.1, hH.2.2 a.1 a.2⟩
  inverse := by sorry

/-- **Proposition** (Subgroups of cyclic groups). Every subgroup of a
cyclic group is cyclic. -/
theorem isCyclicGroup_of_isSubgroup_of_isCyclicGroup {G : Type*} {𝔾 : Group G}
    (hCyc : IsCyclicGroup 𝔾) {H : Set G} (hH : IsSubgroup 𝔾 H) :
    IsCyclicGroup hH.toGroup := by
  sorry

end Subgroups

section QuotientGroups

/-- **Definition.** A subgroup `N` of `G` is **normal** if
`g * n * g⁻¹ ∈ N` for every `g ∈ G`, `n ∈ N`. -/
def IsNormalSubgroup {G : Type*} (𝔾 : Group G) (N : Set G) : Prop :=
  IsSubgroup 𝔾 N ∧ ∀ g : G, ∀ n ∈ N, 𝔾.op (𝔾.op g n) (𝔾.inv g) ∈ N

/-- **Proposition.** The kernel of a group homomorphism is a normal
subgroup of the domain. -/
theorem isNormalSubgroup_ker {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) : IsNormalSubgroup 𝔾 (GroupHom.ker ℍ φ) := by
  sorry

/-- **Definition.** The **left coset** `gH` of `H` by `g`. -/
def leftCoset {G : Type*} (𝔾 : Group G) (g : G) (H : Set G) : Set G :=
  {h | ∃ a ∈ H, h = 𝔾.op g a}

/-- **Definition.** The **right coset** `Hg` of `H` by `g`. -/
def rightCoset {G : Type*} (𝔾 : Group G) (H : Set G) (g : G) : Set G :=
  {h | ∃ a ∈ H, h = 𝔾.op a g}

/-- **Definition.** The equivalence relation `a ~ b ↔ a⁻¹b ∈ N`
corresponding to a (normal) subgroup `N`, whose classes are the left
cosets of `N`. -/
def cosetRel {G : Type*} (𝔾 : Group G) (N : Set G) (a b : G) : Prop :=
  𝔾.op (𝔾.inv a) b ∈ N

/-- **Proposition.** `cosetRel` is an equivalence relation, for `N` a
normal subgroup. -/
theorem equivalence_cosetRel {G : Type*} {𝔾 : Group G} {N : Set G} (hN : IsNormalSubgroup 𝔾 N) :
    Equivalence (cosetRel 𝔾 N) := by
  sorry

/-- The `Setoid` on `G` given by `cosetRel`, for `N` a normal
subgroup. -/
def cosetSetoid {G : Type*} (𝔾 : Group G) {N : Set G} (hN : IsNormalSubgroup 𝔾 N) : Setoid G where
  r := cosetRel 𝔾 N
  iseqv := equivalence_cosetRel hN

/-- **Definition** (Quotient group of `G` modulo `N`). The group
`G/N`, for `N` a normal subgroup of `G`, with operation
`[a] • [b] := [a * b]`. -/
def quotientGroup {G : Type*} (𝔾 : Group G) {N : Set G} (hN : IsNormalSubgroup 𝔾 N) :
    Group (Quotient (cosetSetoid 𝔾 hN)) where
  op := by
    apply Quotient.lift₂ (fun a b => (Quotient.mk (cosetSetoid 𝔾 hN) (𝔾.op a b)))
    sorry
  assoc := by sorry
  e := Quotient.mk (cosetSetoid 𝔾 hN) 𝔾.e
  identity := by sorry
  inv := by
    apply Quotient.lift (fun a => (Quotient.mk (cosetSetoid 𝔾 hN) (𝔾.inv a)))
    sorry
  inverse := by sorry

/-- **Definition.** The quotient map `π : G → G/N`. -/
def quotientMap {G : Type*} (𝔾 : Group G) {N : Set G} (hN : IsNormalSubgroup 𝔾 N) :
    G → Quotient (cosetSetoid 𝔾 hN) :=
  Quotient.mk (cosetSetoid 𝔾 hN)

/-- **Proposition.** The quotient map is a group homomorphism. -/
theorem isGroupHom_quotientMap {G : Type*} (𝔾 : Group G) {N : Set G} (hN : IsNormalSubgroup 𝔾 N) :
    IsGroupHom 𝔾 (quotientGroup 𝔾 hN) (quotientMap 𝔾 hN) := by
  sorry

/-- **Theorem** (Universal property of the quotient). Let `N` be a
normal subgroup of `G`. Then for every group homomorphism
`φ : G → G'` with `N ⊆ ker φ`, there is a unique group homomorphism
`ψ : G/N → G'` with `ψ ∘ π = φ`. -/
theorem exists_unique_quotient_universal_property {G H : Type*} (𝔾 : Group G) {N : Set G}
    (hN : IsNormalSubgroup 𝔾 N) (ℍ : Group H) (φ : G → H) (hφ : IsGroupHom 𝔾 ℍ φ)
    (hker : N ⊆ GroupHom.ker ℍ φ) :
    ∃! ψ : Quotient (cosetSetoid 𝔾 hN) → H,
      IsGroupHom (quotientGroup 𝔾 hN) ℍ ψ ∧ ψ ∘ quotientMap 𝔾 hN = φ := by
  sorry

/-- **Proposition** (kernel ⟺ normal). The kernel of the quotient map
`π : G → G/N` is `N` itself. -/
theorem ker_quotientMap {G : Type*} (𝔾 : Group G) {N : Set G} (hN : IsNormalSubgroup 𝔾 N) :
    GroupHom.ker (quotientGroup 𝔾 hN) (quotientMap 𝔾 hN) = N := by
  sorry

end QuotientGroups

section CanonicalDecompositionAndLagrange

/-- **Theorem** (Canonical decomposition). Every group homomorphism
`φ : G → H` factors as `G ↠ G/ker φ ≅ image φ ↪ H`, where the middle
map is an isomorphism. -/
theorem isomorphicGroups_quotient_ker_image {G H : Type*} {𝔾 : Group G} {ℍ : Group H} {φ : G → H}
    (hφ : IsGroupHom 𝔾 ℍ φ) :
    IsomorphicGroups (quotientGroup 𝔾 (isNormalSubgroup_ker hφ)) (isSubgroup_image hφ).toGroup := by
  sorry

/-- **Corollary** (First isomorphism theorem). If `φ : G → H` is a
surjective group homomorphism, then `H ≅ G/ker φ`. -/
theorem isomorphicGroups_of_surjective_groupHom {G H : Type*} {𝔾 : Group G} {ℍ : Group H}
    {φ : G → H} (hφ : IsGroupHom 𝔾 ℍ φ) (hsurj : Function.Surjective φ) :
    IsomorphicGroups ℍ (quotientGroup 𝔾 (isNormalSubgroup_ker hφ)) := by
  sorry

/-- **Proposition.** If `H₁`, `H₂` are normal subgroups of `G₁`,
`G₂`, then `H₁ × H₂` is a normal subgroup of `G₁ × G₂` and
`(G₁ × G₂)/(H₁ × H₂) ≅ (G₁/H₁) × (G₂/H₂)`. -/
theorem isNormalSubgroup_prod {G1 G2 : Type*} (𝔾1 : Group G1) (𝔾2 : Group G2) {H1 : Set G1}
    {H2 : Set G2} (hH1 : IsNormalSubgroup 𝔾1 H1) (hH2 : IsNormalSubgroup 𝔾2 H2) :
    IsNormalSubgroup (prodGroup 𝔾1 𝔾2) {p : G1 × G2 | p.1 ∈ H1 ∧ p.2 ∈ H2} := by
  sorry

theorem isomorphicGroups_quotient_prod {G1 G2 : Type*} {𝔾1 : Group G1} {𝔾2 : Group G2}
    {H1 : Set G1} {H2 : Set G2} (hH1 : IsNormalSubgroup 𝔾1 H1) (hH2 : IsNormalSubgroup 𝔾2 H2) :
    IsomorphicGroups (quotientGroup (prodGroup 𝔾1 𝔾2) (isNormalSubgroup_prod 𝔾1 𝔾2 hH1 hH2))
      (prodGroup (quotientGroup 𝔾1 hH1) (quotientGroup 𝔾2 hH2)) := by
  sorry

/-- **Definition.** The **index** `[G : H]` of a subgroup `H` in `G`:
the cardinality of the set of left cosets of `H` (`0` if infinite,
matching the convention used for `order`). -/
noncomputable def index {G : Type*} (𝔾 : Group G) (H : Set G) : ℕ :=
  Nat.card {S : Set G // ∃ g : G, S = leftCoset 𝔾 g H}

/-- **Lemma.** For any `g ∈ G`, the maps `H → gH` and `H → Hg`,
`h ↦ gh` and `h ↦ hg`, are bijections. -/
theorem bijective_leftCoset_of_mem {G : Type*} (𝔾 : Group G) (H : Set G) (g : G) :
    Function.Bijective (fun h : H => (⟨𝔾.op g h.1, ⟨h.1, h.2, rfl⟩⟩ : leftCoset 𝔾 g H)) := by
  sorry

/-- **Corollary** (Lagrange's theorem). If `G` is finite and `H` is a
subgroup of `G`, then `|G| = [G : H] * |H|`; in particular, `|H|`
divides `|G|`. -/
theorem card_eq_index_mul_card_subgroup {G : Type*} [Fintype G] (𝔾 : Group G) (H : Set G) :
    Fintype.card G = index 𝔾 H * Nat.card H := by
  sorry

end CanonicalDecompositionAndLagrange

section GroupActions

/-- **Definition** (Action on a set). A function `ρ : G → A → A` is
an **action** of `𝔾` on `A` if `ρ e a = a` for all `a`, and
`ρ (gh) a = ρ g (ρ h a)` for all `g h a`. -/
def IsAction {G A : Type*} (𝔾 : Group G) (ρ : G → A → A) : Prop :=
  (∀ a : A, ρ 𝔾.e a = a) ∧ ∀ g h : G, ∀ a : A, ρ (𝔾.op g h) a = ρ g (ρ h a)

/-- **Definition** (Faithful action). An action is **faithful** if the
identity is the only element fixing every point of `A`. -/
def IsFaithfulAction {G A : Type*} (𝔾 : Group G) (ρ : G → A → A) : Prop :=
  ∀ g : G, (∀ a : A, ρ g a = a) → g = 𝔾.e

/-- **Definition** (Transitive action). An action on a nonempty set
`A` is **transitive** if every point can be reached from every other
by some group element. -/
def IsTransitiveAction {G A : Type*} (_𝔾 : Group G) (ρ : G → A → A) : Prop :=
  ∀ a b : A, ∃ g : G, b = ρ g a

/-- **Definition.** The **orbit** of `a` under an action `ρ` of `𝔾`. -/
def orbit {G A : Type*} (_𝔾 : Group G) (ρ : G → A → A) (a : A) : Set A :=
  {b | ∃ g : G, b = ρ g a}

/-- **Definition.** The **stabilizer** of `a` under an action `ρ` of
`𝔾`: the elements of `G` fixing `a`. -/
def stabilizer {G A : Type*} (_𝔾 : Group G) (ρ : G → A → A) (a : A) : Set G :=
  {g | ρ g a = a}

/-- **Proposition.** Stabilizers are subgroups. -/
theorem isSubgroup_stabilizer {G A : Type*} {𝔾 : Group G} {ρ : G → A → A} (hρ : IsAction 𝔾 ρ)
    (a : A) : IsSubgroup 𝔾 (stabilizer 𝔾 ρ a) := by
  sorry

/-- **Proposition.** If `b = ga`, then `Stab(b) = g • Stab(a) • g⁻¹`. -/
theorem stabilizer_conj {G A : Type*} {𝔾 : Group G} {ρ : G → A → A} (hρ : IsAction 𝔾 ρ) (a : A)
    (g : G) : stabilizer 𝔾 ρ (ρ g a) = {h | ∃ k ∈ stabilizer 𝔾 ρ a, h = 𝔾.op (𝔾.op g k) (𝔾.inv g)} := by
  sorry

/-- **Corollary.** If `O` is an orbit of the action of a finite group
`G` on a set `A`, then `O` is finite and `|O|` divides `|G|`. -/
theorem card_orbit_dvd_card {G A : Type*} [Fintype G] (𝔾 : Group G) {ρ : G → A → A}
    (hρ : IsAction 𝔾 ρ) (a : A) [Fintype (orbit 𝔾 ρ a)] :
    Fintype.card (orbit 𝔾 ρ a) ∣ Fintype.card G := by
  sorry

/-- The **left-multiplication action** of `𝔾` on `G`. -/
def leftMulAction {G : Type*} (𝔾 : Group G) : G → G → G :=
  𝔾.op

theorem isAction_leftMulAction {G : Type*} (𝔾 : Group G) : IsAction 𝔾 (leftMulAction 𝔾) := by
  sorry

/-- **Theorem** (Cayley's theorem). Every group acts faithfully on
some set: the left-multiplication action of `𝔾` on `G` is faithful. -/
theorem isFaithfulAction_leftMulAction {G : Type*} (𝔾 : Group G) :
    IsFaithfulAction 𝔾 (leftMulAction 𝔾) := by
  sorry

end GroupActions

end Algebra0Lean.Groups
