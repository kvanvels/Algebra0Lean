import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Insert
import Mathlib.Data.Quot
import Mathlib.Order.RelClasses
import Mathlib.Tactic.ByContra
import Mathlib.Data.Set.Basic
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Logic.Small.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.PNat.Basic

/-!
# Chapter I: Preliminaries — Set theory and categories

Selected results from Aluffi, *Algebra: Chapter 0*, §I.1 (Naive set
theory) and §I.2 (Functions between sets).
-/

namespace Algebra0Lean.Prelims

/-- A composition operation `comp : Hom B C → Hom A B → Hom A C` for a
family `Hom : I → I → Type*` of "morphism" types indexed by "objects"
`I` is associative if composing in either order gives the same
result. This covers both ordinary function composition (`I := Type*`,
`Hom A B := A → B`, `comp := Function.comp`) and composition in a
`Category` (below) as special cases. -/
def Associative {I : Type*} {Hom : I → I → Type*}
    (comp : ∀ {A B C : I}, Hom B C → Hom A B → Hom A C) : Prop :=
  ∀ {A B C D : I} (f : Hom A B) (g : Hom B C) (h : Hom C D),
    comp h (comp g f) = comp (comp h g) f

section EquivalenceRelationsAndPartitions

variable {X : Type*}

/-- A relation `r` on `X` is reflexive if every element is related to
itself. -/
def IsReflexive (r : X → X → Prop) : Prop := ∀ x, r x x

/-- A relation `r` on `X` is symmetric if `r x y` implies `r y x`. -/
def IsSymmetric (r : X → X → Prop) : Prop := ∀ x y, r x y → r y x

/-- A relation `r` on `X` is transitive if `r x y` and `r y z` imply
`r x z`. -/
def IsTransitive (r : X → X → Prop) : Prop := ∀ x y z, r x y → r y z → r x z

/-- A partition of `X`: a set of nonempty subsets of `X`, every element
of which lies in exactly one of them. -/
def IsPartition (c : Set (Set X)) : Prop :=
  ∅ ∉ c ∧ ∀ a : X, ∃! s ∈ c, a ∈ s

/-- A set of nonempty subsets of `X` is a partition of `X` iff its
members are pairwise disjoint and their union is all of `X`. -/
theorem isPartition_iff_pairwiseDisjoint_cover (c : Set (Set X)) :
    IsPartition c ↔
      ∅ ∉ c ∧
      (∀ s ∈ c, ∀ t ∈ c, s ≠ t → Disjoint s t) ∧
      (∀ a : X, ∃ s ∈ c, a ∈ s) := by
  apply Iff.intro
  · rintro ⟨h0,h1⟩
    apply And.intro h0
    apply And.intro
    · intro s hs t ht hst θ (hθs : θ ⊆ s) (hθt : θ ⊆ t)
      show θ ⊆ ∅
      intro χ hχ
      rcases h1 χ with ⟨L,⟨hL0,hL1⟩,hL2⟩
      have ht := hL2 t ⟨ht,hθt hχ⟩
      have hs := hL2 s ⟨hs,hθs hχ⟩
      rw [←ht] at hs
      exact False.elim (hst hs)
    intro a
    rcases h1 a with ⟨s,hs0,hs1⟩
    use s
  intro ⟨h0,h1,h2⟩
  apply And.intro h0
  · intro a
    rcases h2 a with ⟨s,hs⟩
    use s
    apply And.intro hs
    intro t ⟨ht0,ht1⟩
    specialize h1 s hs.1 t ht0
    contrapose! h1
    apply And.intro
    exact h1.symm

    unfold Disjoint
    push Not
    use {a}
    apply And.intro
    · intro χ
      rw [Set.mem_singleton_iff]
      intro hχ
      rw [←hχ] at hs
      exact hs.2
    apply And.intro
    · intro χ hχ
      rw [Set.mem_singleton_iff] at hχ
      rwa [←hχ] at ht1
    change ¬( ({a}:Set X) ⊆ ∅)
    rw [Set.singleton_subset_iff]
    exact Set.notMem_empty a

/-- Any two members of a partition are either equal or disjoint. (This
is really an exclusive or, since a nonempty set can't be disjoint from
itself, but Lean's standard library has little use for a dedicated
`Xor` connective, so we state it as a plain `∨`.) -/
theorem eq_or_disjoint_of_isPartition {c : Set (Set X)} (hc : IsPartition c) :
     ∀ s ∈ c, ∀ t ∈ c, s = t ∨ Disjoint s t := by
   intro s hs t ht
   rw [isPartition_iff_pairwiseDisjoint_cover] at hc
   rcases hc with ⟨hc0,hc1,hc2⟩
   specialize hc1 s hs t ht
   contrapose! hc1
   exact hc1
      
   
  

/-- In a partition, two members overlap exactly when they are equal. -/
theorem not_disjoint_iff_eq_of_isPartition {c : Set (Set X)} (hc : IsPartition c) :
    ∀ s ∈ c, ∀ t ∈ c, ¬ Disjoint s t ↔ s = t := by
  have h1 := eq_or_disjoint_of_isPartition hc
  intro s hs t ht
  specialize h1 s hs t ht
  apply Iff.intro
  intro h0
  rcases h1 with (h1|h1)
  exact h1
  exact False.elim (h0 h1)
  
  intro h0
  rw [Set.not_disjoint_iff]
  have h1 : s ≠ ∅ := fun h => hc.1 (h ▸ hs)
  rcases Set.nonempty_iff_ne_empty.mpr h1 with ⟨x, hx⟩
  exact ⟨x, hx, h0 ▸ hx⟩
  
  
  

  


/-- The set of equivalence classes of a setoid on `X`. -/
def setoidClasses (r : Setoid X) : Set (Set X) :=
  {s : Set X | ∃ y : X, s = {x : X | x ≈ y}}

/-- **Exercise I.1.2.** The equivalence classes of a setoid on `X` form
a partition of `X`. -/
theorem isPartition_setoidClasses (r : Setoid X) :
    IsPartition (setoidClasses r) := by
  constructor
  intro h0
  unfold setoidClasses at h0
  dsimp at h0
  rcases h0 with ⟨y,hy⟩
  let P : Set X := {x | x ≈ y}
  have h1 : P ⊆ ∅ := by
    rw [hy]
  have h2 : y ∈ P := by
    unfold P
    show y ≈ y
    apply refl
  exact h1 h2
  intro y
  let P : Set X := {x : X| x ≈ y}
  use P
  apply And.intro
  dsimp
  apply And.intro
  unfold setoidClasses
  use y
  unfold P
  show y ≈ y
  apply refl
  intro Q ⟨hQ0,hQ1⟩
  unfold setoidClasses at hQ0
  rcases hQ0 with ⟨q,hQ0⟩
  apply subset_antisymm
  intro z hz
  have h1 : z ≈ y := by
    rw [hQ0] at hz hQ1
    exact Setoid.trans hz (Setoid.symm hQ1)
  unfold P
  exact h1
  intro p hp
  have h1 : p ≈ y := hp
  rw [hQ0] at hQ1
  rw [hQ0]
  unfold P at hp
  show p ≈ q
  clear hp
  have hy : y ≈ q := hQ1
  exact Setoid.trans h1 hy


/-- **Exercise I.1.3.** Every partition of `X` arises as the set of
equivalence classes of some equivalence relation on `X`. -/
theorem exists_setoid_of_isPartition {c : Set (Set X)} (hc : IsPartition c) :
    ∃ r : Setoid X, setoidClasses r = c := by
  have eqOfMem : ∀ {U V : Set X} {p : X}, U ∈ c → V ∈ c → p ∈ U → p ∈ V → U = V := by
    intro U V p hU hV hpU hpV
    exact (not_disjoint_iff_eq_of_isPartition hc U hU V hV).mp
      (fun hd => hd.notMem_of_mem_left hpU hpV)
  rw [isPartition_iff_pairwiseDisjoint_cover] at hc
  rcases hc with ⟨hc0,hc1,hc2⟩
  letI τ : Setoid X := {
    r := fun x y ↦ ∃ U ∈ c, x ∈ U ∧ y ∈ U
    iseqv := {
      refl := by
        intro x
        rcases hc2 x with ⟨U,hU⟩
        use U
        apply And.intro hU.1 (And.intro hU.2 hU.2)
      symm := by
        rintro x y ⟨r,h0⟩
        use r
        apply And.intro h0.1 (And.intro h0.2.2 h0.2.1)
      trans := by
        intro x y z hxy hyz
        rcases hxy with ⟨Uxy,hUxy⟩
        rcases hyz with ⟨Uyz,hUyz⟩
        have h1 : Uxy = Uyz := eqOfMem hUxy.1 hUyz.1 hUxy.2.2 hUyz.2.1
        use Uxy
        apply And.intro hUxy.1 (And.intro hUxy.2.1 _)
        rw [h1]
        exact hUyz.2.2
    }
  }
  have classOf : ∀ {U : Set X} {p : X}, U ∈ c → p ∈ U → U = {x | x ≈ p} := by
    intro U p hU hp
    apply subset_antisymm
    · intro x hx
      exact ⟨U, hU, hx, hp⟩
    · rintro x ⟨V, hV, hxV, hpV⟩
      exact eqOfMem hV hU hpV hp ▸ hxV
  use τ
  unfold setoidClasses
  apply subset_antisymm
  · rintro s ⟨ys, hs1⟩
    rcases hc2 ys with ⟨σ, hσ⟩
    have hσs : σ = s := (classOf hσ.1 hσ.2).trans hs1.symm
    exact hσs ▸ hσ.1
  · rintro T hT
    rcases Set.nonempty_iff_ne_empty.mpr (fun h => hc0 (h ▸ hT)) with ⟨ℓ, hℓ⟩
    exact ⟨ℓ, classOf hT hℓ⟩


/-- The notions of "equivalence relation on `X`" and "partition of
`X`" are really equivalent: `setoidClasses` is a bijection from
equivalence relations on `X` to partitions of `X`. -/
theorem bijective_setoidClasses_subtype :
    Function.Bijective (fun r : Setoid X =>
      (⟨setoidClasses r, isPartition_setoidClasses r⟩ :
        {c : Set (Set X) // IsPartition c})) := by
  sorry

/-- **Exercise I.1.4** (generalized to `n` elements). The number of
equivalence relations on a set of `n` elements is the `n`th Bell number. -/
theorem card_setoid_fin_eq_bell (n : ℕ) :
    Nat.card (Setoid (Fin n)) = Nat.bell n := by
  sorry

/-- **Exercise I.1.5.** There is a relation that is reflexive and
symmetric but not transitive. -/
theorem exists_reflexive_symmetric_not_transitive :
    ∃ (Y : Type) (r : Y → Y → Prop), IsReflexive r ∧ IsSymmetric r ∧ ¬ IsTransitive r := by
  sorry

/-- The relation `a ∼ b ↔ b - a ∈ ℤ` on `ℝ`. -/
def modZRelation (a b : ℝ) : Prop := ∃ k : ℤ, b - a = (k : ℝ)

/-- **Exercise I.1.6** (first part). `modZRelation` is an equivalence
relation on `ℝ`. -/
theorem equivalence_modZRelation : Equivalence modZRelation := {
  refl := by
    intro x
    use 0
    simp only [sub_self, Int.cast_zero]
  symm := by
    intro x y ⟨k,hkxy⟩
    use -k
    simp only [Int.cast_neg]
    rw [←hkxy,neg_sub]
  trans := by
    intro x y z ⟨k,hkxy⟩ ⟨ℓ,hlyz⟩
    use (k + ℓ)
    simp only [Int.cast_add]
    rw [←hkxy,←hlyz]
    ring_nf
}



/-- The relation on `ℝ × ℝ` identifying points that differ by an
integer vector in each coordinate. -/
def modZRelationPlane (a b : ℝ × ℝ) : Prop :=
  modZRelation a.1 b.1 ∧ modZRelation a.2 b.2

/-- **Exercise I.1.6** (second part). `modZRelationPlane` is an
equivalence relation on `ℝ × ℝ`. -/
theorem equivalence_modZRelationPlane : Equivalence modZRelationPlane := by
  sorry


end EquivalenceRelationsAndPartitions

section InjectiveSurjectiveInverses

variable {X Y : Type*}

/-- The graph of `f : X → Y`. -/
def graphOf (f : X → Y) : Set (X × Y) := {p | p.2 = f p.1}

/-- A subset `Γ ⊆ X × Y` is the graph of a function `X → Y` iff every
`a` has exactly one `b` with `(a, b) ∈ Γ`: this is the requirement a
subset of `X × Y` must satisfy in order to be (the graph of) a
function. -/
def IsGraph (Γ : Set (X × Y)) : Prop := ∀ a : X, ∃! b : Y, (a, b) ∈ Γ

/-- The graph of a function satisfies `IsGraph`. -/
theorem isGraph_graphOf (f : X → Y) : IsGraph (graphOf f) := by
  intro x
  unfold graphOf
  use (f x)
  dsimp
  apply And.intro rfl
  intro y h0
  exact h0


/-- **A function really "is" its graph.** `graphOf` is a bijection
between functions `X → Y` and subsets of `X × Y` satisfying
`IsGraph`. -/
theorem bijective_graphOf :
    Function.Bijective (fun f : X → Y =>
      (⟨graphOf f, isGraph_graphOf f⟩ : {Γ : Set (X × Y) // IsGraph Γ})) := by
  apply And.intro
  intro f0 f1 hf0f1
  simp only [Subtype.mk.injEq] at hf0f1
  unfold graphOf at hf0f1
  apply funext
  intro θ
  have h1 : (θ,f0 θ) ∈ {p | p.2 = f0 p.1} := by rfl
  rw [hf0f1] at h1
  simp at h1
  exact h1
  intro Γf
  unfold IsGraph at Γf
  let f := fun a => (Γf.2 a).choose
  let hf := fun a => (Γf.2 a).choose_spec.1
  dsimp at hf
  use f
  apply Subtype.ext
  apply subset_antisymm
  rintro ⟨x,y⟩ hxy
  unfold graphOf at hxy
  dsimp at hxy
  rw [hxy]
  exact hf x
  rintro ⟨x,y⟩ hxy
  simp
  unfold graphOf
  show y = f x
  have h1 := (Γf.2 x).choose_spec.2 y hxy
  exact h1
  

  
  
  
  
  
  
  
  
  
  
  
      

/-- Composition of functions is associative. -/
theorem comp_assoc : Associative (@Function.comp) := by
  intro A B C D f g h
  apply funext
  intro x
  simp only [Function.comp_apply]
  


/-- The identity function is a left unit for composition. -/
theorem id_comp (f : X → Y) : (id : Y → Y) ∘ f = f := by
  apply funext
  intro x
  simp only [Function.comp_apply,id_eq]
    

/-- The identity function is a right unit for composition. -/
theorem comp_id (f : X → Y) : f ∘ (id : X → X) = f := by
  apply funext
  intro x
  simp only [Function.comp_apply,id_eq]
  

/-- Two types are isomorphic if there is a bijection between them. -/
def Isomorphic (A B : Type*) : Prop := Nonempty (A ≃ B)

/-- The identity function is a bijection. -/
theorem bijective_id : Function.Bijective (id : X → X) := by
  constructor
  · intro x0 x1 h0
    rwa [id_eq,id_eq] at h0
  intro y
  use y
  rw [id_eq]
  

/-- If `X` is finite and isomorphic to `Y`, then `Y` is finite too, and
`X`, `Y` have the same cardinality. -/
theorem finite_and_card_eq_of_isomorphic [Finite X] (h : Isomorphic X Y) :
    Finite Y ∧ Nat.card X = Nat.card Y := by
  sorry

/-- The tagging map `a ↦ ((), a)` from `X` to `Unit × X` is a
bijection. -/
theorem bijective_unitProdMk :
    Function.Bijective (fun a : X => ((), a) : X → Unit × X) := by
  sorry

/-- **Proposition I.2.4.** Assume `X` is nonempty, and let `f : X → Y`
be a function. Then `f` has a left-inverse if and only if it is
injective. -/
theorem hasLeftInverse_iff_injective [Nonempty X] (f : X → Y) :
    Function.HasLeftInverse f ↔ Function.Injective f := by
  apply Iff.intro
  · rintro ⟨g, hg⟩ a b hab
    rw [← hg a, ← hg b, hab]
  · intro hf
    classical
    refine ⟨fun y ↦ if h : ∃ x, f x = y then h.choose else Classical.arbitrary X, ?_⟩
    intro x
    have hex : ∃ a, f a = f x := ⟨x, rfl⟩
    simp only [dif_pos hex]
    exact hf hex.choose_spec

/-- **Proposition I.2.4** (second part). `f` has a right-inverse if
and only if it is surjective. -/
theorem hasRightInverse_iff_surjective (f : X → Y) :
    Function.HasRightInverse f ↔ Function.Surjective f := by
  apply Iff.intro
  · rintro ⟨g, hg⟩ y
    exact ⟨g y, hg y⟩
  · intro hf
    classical
    exact ⟨fun y ↦ (hf y).choose, fun y ↦ (hf y).choose_spec⟩

/-- **Corollary I.2.5.** A function is a bijection if and only if it
has a (two-sided) inverse. -/
theorem bijective_iff_hasInverse [Nonempty X] (f : X → Y) :
    Function.Bijective f ↔
      ∃ g : Y → X, Function.LeftInverse g f ∧ Function.RightInverse g f := by
  apply Iff.intro
  · rintro ⟨hinj, hsurj⟩
    rcases (hasRightInverse_iff_surjective f).mpr hsurj with ⟨g, hg⟩
    refine ⟨g, ?_, hg⟩
    intro x
    apply hinj
    exact hg (f x)
  · rintro ⟨g, hgl, hgr⟩
    exact ⟨hgl.injective, hgr.surjective⟩

/-- If `f` is injective but not surjective, it has no right-inverse. -/
theorem not_hasRightInverse_of_injective_not_surjective {f : X → Y}
    (hf : Function.Injective f) (hf' : ¬ Function.Surjective f) :
    ¬ Function.HasRightInverse f := by
  sorry

/-- If `f` is injective but not surjective, and `X` has at least two
elements, then `f` has more than one left-inverse. -/
theorem exists_ne_leftInverse_of_injective_not_surjective {f : X → Y}
    (hf : Function.Injective f) (hf' : ¬ Function.Surjective f)
    (hX : ∃ x₁ x₂ : X, x₁ ≠ x₂) :
    ∃ g₁ g₂ : Y → X, Function.LeftInverse g₁ f ∧ Function.LeftInverse g₂ f ∧ g₁ ≠ g₂ := by
  sorry



/- NOTE: No realy purpose of this is there? -/
/-- A right-inverse of `f` is also called a *section* of `f`. -/
def IsSection (f : X → Y) (g : Y → X) : Prop := Function.RightInverse g f

/-- If `f` is surjective and some fiber of `f` has at least two
elements, then `f` has more than one right-inverse (section). -/
theorem exists_ne_section_of_surjective {f : X → Y} (hf : Function.Surjective f)
    (h : ∃ (y : Y) (x₁ x₂ : X), f x₁ = y ∧ f x₂ = y ∧ x₁ ≠ x₂) :
    ∃ g₁ g₂ : Y → X, IsSection f g₁ ∧ IsSection f g₂ ∧ g₁ ≠ g₂ := by
  sorry

/-- The fiber of `f` over `q`: the set of all elements mapping to
`q`. -/
def fiber (f : X → Y) (q : Y) : Set X := {a : X | f a = q}

/-- `f` is surjective iff every fiber is nonempty. -/
theorem surjective_iff_forall_fiber_nonempty (f : X → Y) :
    Function.Surjective f ↔ ∀ q : Y, (fiber f q).Nonempty := by
  sorry

/-- `f` is injective iff every fiber is a subsingleton (has at most
one element). -/
theorem injective_iff_forall_fiber_subsingleton (f : X → Y) :
    Function.Injective f ↔ ∀ q : Y, (fiber f q).Subsingleton := by
  apply Iff.intro
  · intro h0 z
    unfold fiber
    intro x (hx : f x = z) y (hy : f y = z)
    apply h0
    rw [hx]
    exact hy.symm
  intro h0 x0 x1 h1  
  specialize h0 (f x0)
  have h2 := @h0 x0 rfl x1 (by rw [h1]; rfl)
  exact h2
  

/-- For a bijective `f` with two-sided inverse `g`, the forward image
under `g` of a subset agrees with the preimage under `f`. -/
theorem image_inverse_eq_preimage {f : X → Y} {g : Y → X}
    (hgl : Function.LeftInverse g f) (hgr : Function.RightInverse g f) (T : Set Y) :
    g '' T = f ⁻¹' T := by
  apply subset_antisymm
  intro x ⟨y,hy0,hy1⟩
  rw [←hy1]
  show f (g y) ∈ T
  have h1 : f (g y) = y := hgr y
  rwa [h1]
  intro x (hx : f x ∈ T)
  use (f x)
  apply And.intro hx
  exact hgl x
  
  


/-- **Exercise I.2.3** (first part). The inverse of a bijection is a
bijection. -/
theorem bijective_invFun [Nonempty X] {f : X → Y} (hf : Function.Bijective f) :
    Function.Bijective (Function.invFun f) := by
  rcases hf with ⟨hf1,hf2⟩
  constructor
  · intro y0 y1 h0
    have h2 := by calc
      y0 = f (Function.invFun f y0) := by exact (Function.invFun_eq (hf2 y0)).symm
       _ = f (Function.invFun f y1) := by rw [h0]
       _ = y1 := by exact Function.invFun_eq (hf2 y1)
    exact h2
  · intro x
    use (f x)
    exact Function.leftInverse_invFun hf1 x


/-- **Exercise I.2.3** (second part). The composite of two bijections
is a bijection. -/
theorem bijective_comp {Z : Type*} {f : X → Y} {g : Y → Z}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (g ∘ f) := by
  rcases hf with ⟨hfInj,hfSurj⟩
  rcases hg with ⟨hgInj,hgSurj⟩
  apply And.intro
  intro x0 x1 hgf01
  apply hfInj 
  apply hgInj
  exact hgf01
  intro z
  rcases hgSurj z with ⟨y,hz⟩
  rcases hfSurj y with ⟨x,hy⟩
  use x
  rw [←hz,←hy]
  rfl

/-- **Exercise I.2.4** (first part). Isomorphism of sets is
reflexive, symmetric, and transitive. -/
theorem isomorphic_refl : IsReflexive Isomorphic := by
   intro A
   use id
   use id
   exact (fun x => rfl)
   exact (fun x => rfl)


theorem isomorphic_symm : IsSymmetric Isomorphic := by
  intro A B h
  rcases h with ⟨T,Tinv,hT0,hT1⟩
  use Tinv, T
  intro b
  exact hT1 b
  intro a
  exact hT0 a


theorem isomorphic_trans : IsTransitive Isomorphic := by
  intro A B C ⟨fAB,finvAB,hAB0,hAB1⟩  ⟨fBC,finvBC,hBC0,hBC1⟩
  use (fBC ∘ fAB), (finvAB ∘ finvBC)
  intro a
  simp only [Function.comp_apply]
  rw [hBC0 (fAB a),hAB0 a]
  intro c
  simp only [Function.comp_apply]
  rw [hAB1 (finvBC c),hBC1 c]
  

/-- **Exercise I.2.7.** The graph of `f : X → Y` is isomorphic to
`X`. -/
theorem isomorphic_graph (f : X → Y) :
    Isomorphic {p : X × Y // p.2 = f p.1} X := by
  sorry

end InjectiveSurjectiveInverses

section MonomorphismsAndEpimorphisms

universe u
variable {X Y : Type u}

/-- `f` is a monomorphism: it is left-cancellable when precomposed with
any function out of an arbitrary set `Z`. -/
def Monomorphic (f : X → Y) : Prop :=
  ∀ (Z : Type u) (g g' : Z → X), f ∘ g = f ∘ g' → g = g'

/-- `f` is an epimorphism: any function out of `Y` factors through `f`
after precomposing with some function into `X`. -/
def Epimorphic (f : X → Y) : Prop :=
  ∀ (Z : Type u) (g : Z → Y), ∃ h : Z → X, f ∘ h = g

/-- **Proposition I.2.3.** A function is injective if and only if it is
a monomorphism. -/
theorem injective_iff_monomorphic (f : X → Y) [Nonempty X] :
    Function.Injective f ↔ Monomorphic f := by
  apply Iff.intro
  intro h0 Z g0 g1 h01
  apply funext
  intro z
  have h1 := congr_fun h01 z
  
  exact @h0 (g0 z) (g1 z) h1  
  intro h0 a0 a1 h1
  specialize h0 X (fun x ↦ a0) (fun x ↦ a1) ?_
  funext θ
  exact h1
  have h2 : ∃ y : X, True := (exists_const X).mpr trivial
  rcases h2 with ⟨y,hy⟩
  
  have h1 := congr_fun h0  y
  exact h1

/-- **Exercise I.2.5.** A function is surjective if and only if it is
an epimorphism. -/
theorem epimorphic_iff_surjective (f : X → Y) :
    Epimorphic f ↔ Function.Surjective f := by
  apply Iff.intro
  intro h0 y
  unfold Epimorphic at h0
  specialize h0 Y id
  rcases h0 with ⟨finv,hfinv⟩
  use (finv y)
  
  rw [←@Function.comp_apply X Y Y f finv y,hfinv,id_eq]
  
  rintro h0 Z g

  have h1 := h0.hasRightInverse
  unfold Function.HasRightInverse at h1
  rcases h1 with ⟨finv,hfinv⟩
  clear h0
  use finv ∘ g

  unfold Function.RightInverse at hfinv
  unfold Function.LeftInverse at hfinv
  apply funext
  intro z
  rw [←Function.comp_assoc,Function.comp_apply]
  exact hfinv (g z)

end MonomorphismsAndEpimorphisms

section CanonicalDecomposition

variable {X Y : Type*}

/-- The equivalence relation on `X` induced by a function `f : X → Y`,
identifying `x`, `x'` whenever `f x = f x'`. -/
def kernelPairSetoid (f : X → Y) : Setoid X where
  r a b := f a = f b
  iseqv := {
    refl := fun _ ↦ rfl
    symm := fun h ↦ h.symm
    trans := by
      intro x y z h0 h1
      rwa [h0]
  }

/-- The canonical (surjective) projection `X ↠ X/∼` of
`Theorem I.2.8`. -/
def canonicalProjection (f : X → Y) : X → Quotient (kernelPairSetoid f) :=
  fun a ↦ ⟦a⟧

theorem canonicalProjection_surjective (f : X → Y) :
    (canonicalProjection f).Surjective := by
  intro p
  rcases Quotient.exists_rep p with ⟨a, ha⟩
  exact ⟨a, ha⟩



/-- The induced bijection `X/∼ ≅ image f` of `Theorem I.2.8`. -/
def canonicalBijection (f : X → Y) :
    Quotient (kernelPairSetoid f) → Set.range f := fun x ↦
  ⟨Quotient.lift f (fun _ _ h ↦ h) x, by
    rcases Quotient.exists_rep x with ⟨a, rfl⟩
    exact ⟨a, rfl⟩⟩

theorem canonicalBijection_bijective (f : X → Y) :
    (canonicalBijection f).Bijective := by
  apply And.intro
  · intro x0 x1 h01
    rcases Quotient.exists_rep x0 with ⟨a0, rfl⟩
    rcases Quotient.exists_rep x1 with ⟨a1, rfl⟩
    have h1 : f a0 = f a1 := congrArg Subtype.val h01
    exact Quotient.sound h1
  · rintro ⟨y, a, rfl⟩
    exact ⟨⟦a⟧, rfl⟩

/-- The canonical (injective) inclusion `image f ↪ Y` of
`Theorem I.2.8`. -/
def canonicalInclusion (f : X → Y) : Set.range f → Y := fun x ↦ x.val

theorem canonicalInclusion_injective (f : X → Y) :
    (canonicalInclusion f).Injective := by
  intro ⟨y0,⟨x0,h0⟩⟩ ⟨y1,⟨x1,h1⟩ ⟩ h2  
  unfold canonicalInclusion at h2
  rcases h2 with ⟨h20,h21⟩
  rfl
    

/-- **Theorem I.2.8** (canonical decomposition of a function). Every
function factors as a surjection, followed by a bijection, followed by
an injection. -/
theorem canonicalDecomposition (f : X → Y) :
    f = canonicalInclusion f ∘ canonicalBijection f ∘ canonicalProjection f := by
  apply funext
  intro θ
  simp
  unfold canonicalProjection
  unfold canonicalBijection
  unfold canonicalInclusion  
  simp only [Quotient.lift_mk]  

end CanonicalDecomposition

section Categories

universe u v

/-- A category: a type of objects, a type of morphisms between each
pair of objects, identities, and an associative, unital composition
law. -/
structure Category where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : ∀ A, Hom A A
  comp : ∀ {A B C}, Hom B C → Hom A B → Hom A C
  comp_assoc : Associative (@comp)
  id_comp : ∀ {A B} (f : Hom A B), comp (id B) f = f
  comp_id : ∀ {A B} (f : Hom A B), comp f (id A) = f

/-- A category is small (relative to universe `w`) if its class of
objects is actually (equivalent to) a type in `Type w`. -/
def Category.IsSmall.{w} (C : Category.{u, v}) : Prop := Small.{w} C.Obj

/-- The endomorphisms of an object `A`: morphisms from `A` to
itself. -/
def Category.End (C : Category.{u, v}) (A : C.Obj) : Type v := C.Hom A A

/-- **The category of types.** Objects are types (in `Type w`);
morphisms are functions. -/
def typeCategory.{w} : Category.{w + 1, w} where
  Obj := Type w
  Hom A B := A → B
  id _ := id
  comp := Function.comp
  comp_assoc := comp_assoc
  id_comp := id_comp
  comp_id := comp_id

/-- **The category induced by a preorder.** Given a reflexive,
transitive relation `r` on `S`, the category with objects `S` and
exactly one morphism `a ⟶ b` when `a` is related to `b` (and none
otherwise). -/
def preorderCategory {S : Type u} {r : S → S → Prop}
    (hrefl : IsReflexive r) (htrans : IsTransitive r) : Category.{u, 0} where
  Obj := S
  Hom a b := PLift (r a b)
  id a := ⟨hrefl a⟩
  comp g f := ⟨htrans _ _ _ f.down g.down⟩
  comp_assoc := by
    intro A B C D f g h
    rfl

  id_comp := by
    intros
    rfl
  comp_id := by
    intros
    rfl

/-- **Discrete categories.** The category induced (via
`preorderCategory`) by the equality relation on `S`: the only
morphisms are the identities. -/
def discreteCategory (S : Type u) : Category.{u, 0} :=
  preorderCategory (S := S) (r := Eq)
  ((congrFun ∘ fun a ↦ a) rfl)
  (@Trans.trans S S S Eq Eq Eq (instTransEq Eq))

/-- **The category of a preorder.** Given a preorder `≤` on `S`
(e.g. `ℤ` with its usual order), the induced category. -/
def leCategory (S : Type u) [Preorder S] : Category.{u, 0} :=
  preorderCategory (S := S) (r := (· ≤ ·)) (by sorry) (by sorry)

/-- **Slice category.** Given a category `C` and an object `A`, the
category `C_A` of morphisms into `A`: objects are pairs `(Z, f : Z ⟶
A)`, and a morphism `(Z₁,f₁) ⟶ (Z₂,f₂)` is a morphism `σ : Z₁ ⟶ Z₂` of
`C` with `f₂ ∘ σ = f₁`. -/
def sliceCategory (C : Category.{u, v}) (A : C.Obj) : Category where
  Obj := Σ Z : C.Obj, C.Hom Z A
  Hom X Y := {σ : C.Hom X.1 Y.1 // C.comp Y.2 σ = X.2}
  id X := ⟨C.id X.1, by sorry⟩
  comp g f := ⟨C.comp g.1 f.1, by sorry⟩
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **Coslice category.** Given a category `C` and an object `A`, the
category `C^A` of morphisms out of `A`: objects are pairs `(Z, f : A
⟶ Z)`, and a morphism `(Z₁,f₁) ⟶ (Z₂,f₂)` is a morphism `σ : Z₁ ⟶ Z₂`
of `C` with `σ ∘ f₁ = f₂`. -/
def coSliceCategory (C : Category.{u, v}) (A : C.Obj) : Category where
  Obj := Σ Z : C.Obj, C.Hom A Z
  Hom X Y := {σ : C.Hom X.1 Y.1 // C.comp σ X.2 = Y.2}
  id X := ⟨C.id X.1, by sorry⟩
  comp g f := ⟨C.comp g.1 f.1, by sorry⟩
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **Pointed sets.** The category of pointed sets, obtained as the
coslice category of `typeCategory` under the singleton type: objects
are pairs `(S, f : PUnit ⟶ S)` (that is, a set `S` together with a
distinguished element `f ⟨⟩`), and morphisms are functions preserving
the basepoint. -/
def pointedSetCategory.{w} : Category := coSliceCategory typeCategory.{w} PUnit

/-- **Two-leg category.** Given a category `C` and two objects `A`,
`B`, the category `C_{A,B}` of pairs of morphisms into `A` and `B`
from a common source: objects are triples `(Z, f : Z ⟶ A, g : Z ⟶
B)`, and a morphism `(Z₁,f₁,g₁) ⟶ (Z₂,f₂,g₂)` is `σ : Z₁ ⟶ Z₂` with
`f₂ ∘ σ = f₁` and `g₂ ∘ σ = g₁`. -/
def twoLegCategory (C : Category.{u, v}) (A B : C.Obj) : Category where
  Obj := Σ Z : C.Obj, C.Hom Z A × C.Hom Z B
  Hom X Y := {σ : C.Hom X.1 Y.1 // C.comp Y.2.1 σ = X.2.1 ∧ C.comp Y.2.2 σ = X.2.2}
  id X := ⟨C.id X.1, by sorry, by sorry⟩
  comp g f := ⟨C.comp g.1 f.1, by sorry, by sorry⟩
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **Two-leg co-category.** Given a category `C` and two objects `A`,
`B`, the category `C^{A,B}` of pairs of morphisms out of `A` and `B`
into a common target: objects are triples `(Z, f : A ⟶ Z, g : B ⟶
Z)`, and a morphism `(Z₁,f₁,g₁) ⟶ (Z₂,f₂,g₂)` is `σ : Z₁ ⟶ Z₂` with
`σ ∘ f₁ = f₂` and `σ ∘ g₁ = g₂`. -/
def twoLegCoCategory (C : Category.{u, v}) (A B : C.Obj) : Category where
  Obj := Σ Z : C.Obj, C.Hom A Z × C.Hom B Z
  Hom X Y := {σ : C.Hom X.1 Y.1 // C.comp σ X.2.1 = Y.2.1 ∧ C.comp σ X.2.2 = Y.2.2}
  id X := ⟨C.id X.1, by sorry, by sorry⟩
  comp g f := ⟨C.comp g.1 f.1, by sorry, by sorry⟩
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **Fibered category.** Given a category `C` and two morphisms
`α : A ⟶ T`, `β : B ⟶ T` with common target, the category `C_{α,β}`
of commuting pairs `(f : Z ⟶ A, g : Z ⟶ B)` with `α ∘ f = β ∘ g`. -/
def fiberedCategory (C : Category.{u, v}) {A B T : C.Obj}
    (α : C.Hom A T) (β : C.Hom B T) : Category where
  Obj := {p : Σ Z : C.Obj, C.Hom Z A × C.Hom Z B // C.comp α p.2.1 = C.comp β p.2.2}
  Hom X Y := {σ : C.Hom X.1.1 Y.1.1 // C.comp Y.1.2.1 σ = X.1.2.1 ∧ C.comp Y.1.2.2 σ = X.1.2.2}
  id X := ⟨C.id X.1.1, by sorry, by sorry⟩
  comp g f := ⟨C.comp g.1 f.1, by sorry, by sorry⟩
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **Exercise (opposite category).** The opposite category `C^op`:
same objects, with `Hom` reversed. -/
def Category.op (C : Category.{u, v}) : Category.{u, v} where
  Obj := C.Obj
  Hom A B := C.Hom B A
  id A := C.id A
  comp g f := C.comp f g
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **Exercise.** How large is `End_Set(A)` for a finite set `A`? -/
theorem card_end_typeCategory (A : Type u) [Fintype A] :
    Nat.card (Category.End typeCategory A) = Nat.card A ^ Nat.card A := by
  sorry

/-- **Exercise.** The strict order `<` on `ℤ` is not reflexive, so
`preorderCategory` cannot be applied to it: there is no category in
the style of `leCategory` built from `<`. -/
theorem not_isReflexive_lt_int : ¬ IsReflexive ((· < ·) : ℤ → ℤ → Prop) := by
  sorry

/-- **Exercise (category of matrices).** Objects are natural numbers;
morphisms `n ⟶ m` are `m × n` real matrices, with composition given
by matrix multiplication. -/
def matrixCategory : Category.{0, 0} where
  Obj := ℕ
  Hom n m := Matrix (Fin m) (Fin n) ℝ
  id _ := 1
  comp g f := g * f
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **Exercise (subcategory).** A subcategory of `C`: a predicate on
objects, together with a predicate on morphisms between them that
contains all identities and is closed under composition. -/
structure Subcategory (C : Category.{u, v}) where
  ObjPred : C.Obj → Prop
  HomPred : ∀ {A B}, ObjPred A → ObjPred B → C.Hom A B → Prop
  id_mem : ∀ {A} (hA : ObjPred A), HomPred hA hA (C.id A)
  comp_mem : ∀ {A B D} (hA : ObjPred A) (hB : ObjPred B) (hD : ObjPred D)
      {f : C.Hom A B} {g : C.Hom B D},
      HomPred hA hB f → HomPred hB hD g → HomPred hA hD (C.comp g f)

/-- A subcategory is full if it contains every morphism (of `C`)
between two of its objects. -/
def Subcategory.IsFull {C : Category.{u, v}} (S : Subcategory C) : Prop :=
  ∀ {A B} (hA : S.ObjPred A) (hB : S.ObjPred B) (f : C.Hom A B), S.HomPred hA hB f

/-- **Exercise.** The infinite types form a full subcategory of the
category of types. -/
def infiniteSubcategory.{w} : Subcategory typeCategory.{w} where
  ObjPred A := Infinite A
  HomPred _ _ _ := True
  id_mem _ := by sorry
  comp_mem := by sorry

theorem infiniteSubcategory_isFull.{w} : infiniteSubcategory.{w}.IsFull := by
  sorry

end Categories

section Morphisms

universe u v

/-- A morphism `f : A ⟶ B` is an isomorphism if it has a two-sided
inverse under composition. -/
def Category.IsIso (C : Category.{u, v}) {A B : C.Obj} (f : C.Hom A B) : Prop :=
  ∃ g : C.Hom B A, C.comp g f = C.id A ∧ C.comp f g = C.id B

/-- **The inverse of an isomorphism is unique.** -/
theorem Category.isIso_inverse_unique (C : Category.{u, v}) {A B : C.Obj} {f : C.Hom A B}
    {g1 g2 : C.Hom B A} (hg1 : C.comp g1 f = C.id A ∧ C.comp f g1 = C.id B)
    (hg2 : C.comp g2 f = C.id A ∧ C.comp f g2 = C.id B) : g1 = g2 := by
  sorry

/-- If `f` has a left-inverse `g₁` and a right-inverse `g₂`, then `f`
is an isomorphism, `g₁ = g₂`, and this common morphism is the inverse
of `f`. -/
theorem Category.isIso_of_hasLeftInverse_hasRightInverse (C : Category.{u, v}) {A B : C.Obj}
    {f : C.Hom A B} {g1 g2 : C.Hom B A} (h1 : C.comp g1 f = C.id A)
    (h2 : C.comp f g2 = C.id B) : C.IsIso f ∧ g1 = g2 := by
  sorry

/-- The inverse of an isomorphism. -/
noncomputable def Category.IsIso.inv {C : Category.{u, v}} {A B : C.Obj} {f : C.Hom A B}
    (hf : C.IsIso f) : C.Hom B A := hf.choose

/-- **Iso properties** (existence part). Each identity is an
isomorphism; the inverse of an isomorphism is again an isomorphism;
and the composite of two isomorphisms is an isomorphism. -/
theorem Category.isIso_id (C : Category.{u, v}) (A : C.Obj) : C.IsIso (C.id A) := by
  sorry

theorem Category.IsIso.isIso_inv {C : Category.{u, v}} {A B : C.Obj} {f : C.Hom A B}
    (hf : C.IsIso f) : C.IsIso hf.inv := by
  sorry

theorem Category.IsIso.isIso_comp {C : Category.{u, v}} {A B D : C.Obj} {f : C.Hom A B}
    {g : C.Hom B D} (hf : C.IsIso f) (hg : C.IsIso g) : C.IsIso (C.comp g f) := by
  sorry

/-- **Iso properties** (equations). Each identity is its own inverse;
taking the inverse twice recovers the original morphism; and the
inverse of a composite reverses the order:
`(g ∘ f)⁻¹ = f⁻¹ ∘ g⁻¹`. -/
theorem Category.inv_id (C : Category.{u, v}) (A : C.Obj) :
    (C.isIso_id A).inv = C.id A := by
  sorry

theorem Category.IsIso.inv_inv {C : Category.{u, v}} {A B : C.Obj} {f : C.Hom A B}
    (hf : C.IsIso f) : hf.isIso_inv.inv = f := by
  sorry

theorem Category.IsIso.inv_comp {C : Category.{u, v}} {A B D : C.Obj} {f : C.Hom A B}
    {g : C.Hom B D} (hf : C.IsIso f) (hg : C.IsIso g) :
    (hf.isIso_comp hg).inv = C.comp hf.inv hg.inv := by
  sorry

/-- Two objects of a category are isomorphic if there is an
isomorphism between them. -/
def Category.ObjIso (C : Category.{u, v}) (A B : C.Obj) : Prop :=
  ∃ f : C.Hom A B, C.IsIso f

/-- **`ObjIso` is an equivalence relation** (an immediate corollary of
the iso properties above). -/
theorem Category.objIso_refl (C : Category.{u, v}) (A : C.Obj) : C.ObjIso A A := by
  sorry

theorem Category.objIso_symm (C : Category.{u, v}) {A B : C.Obj} (h : C.ObjIso A B) :
    C.ObjIso B A := by
  sorry

theorem Category.objIso_trans (C : Category.{u, v}) {A B D : C.Obj} (h1 : C.ObjIso A B)
    (h2 : C.ObjIso B D) : C.ObjIso A D := by
  sorry

/-- A category is a **groupoid** if every morphism is an
isomorphism. -/
def Category.IsGroupoid (C : Category.{u, v}) : Prop := ∀ {A B} (f : C.Hom A B), C.IsIso f

/-- An **automorphism** of `A`: an isomorphism from `A` to itself. -/
def Category.Aut (C : Category.{u, v}) (A : C.Obj) : Type v := {f : C.End A // C.IsIso f}

/-- A morphism `f : A ⟶ B` is a **monomorphism** if it is
left-cancellable when precomposed with any pair of morphisms into
`A`. -/
def Category.IsMono (C : Category.{u, v}) {A B : C.Obj} (f : C.Hom A B) : Prop :=
  ∀ {Z : C.Obj} (a1 a2 : C.Hom Z A), C.comp f a1 = C.comp f a2 → a1 = a2

/-- A morphism `f : A ⟶ B` is an **epimorphism** if it is
right-cancellable when postcomposed with any pair of morphisms out of
`B`. -/
def Category.IsEpi (C : Category.{u, v}) {A B : C.Obj} (f : C.Hom A B) : Prop :=
  ∀ {Z : C.Obj} (b1 b2 : C.Hom B Z), C.comp b1 f = C.comp b2 f → b1 = b2

/-- In a category induced by a preorder, every morphism is both a
monomorphism and an epimorphism (there is at most one morphism
between any two objects, so the cancellation conditions are
vacuous). -/
theorem isMono_and_isEpi_preorderCategory {S : Type u} {r : S → S → Prop}
    (hrefl : IsReflexive r) (htrans : IsTransitive r) {a b : S}
    (f : (preorderCategory hrefl htrans).Hom a b) :
    (preorderCategory hrefl htrans).IsMono f ∧ (preorderCategory hrefl htrans).IsEpi f := by
  sorry

/-- In the category of types, a function is an isomorphism iff it is
both injective and surjective, i.e. iff it is both a monomorphism and
an epimorphism. -/
theorem isIso_iff_bijective_typeCategory {A B : Type u} (f : (typeCategory).Hom A B) :
    (typeCategory).IsIso f ↔ Function.Bijective f := by
  sorry

/-- **Exercise (generalized associativity), base case beyond ternary.**
Composing a chain of four morphisms gives the same result regardless
of how parentheses are inserted. (The fully general `n`-ary statement
needs a dependent notion of "chain of `n` composable morphisms";
this is the next case after `Associative` illustrating the pattern.) -/
theorem Category.comp_assoc4 (C : Category.{u, v}) {A B D E F : C.Obj}
    (f : C.Hom A B) (g : C.Hom B D) (h : C.Hom D E) (i : C.Hom E F) :
    C.comp i (C.comp h (C.comp g f)) = C.comp (C.comp (C.comp i h) g) f := by
  sorry

/-- **Exercise.** The category induced by a preorder is a groupoid
exactly when the relation is also symmetric (that is, when it is an
equivalence relation). -/
theorem isGroupoid_preorderCategory_iff {S : Type u} {r : S → S → Prop}
    (hrefl : IsReflexive r) (htrans : IsTransitive r) :
    (preorderCategory hrefl htrans).IsGroupoid ↔ IsSymmetric r := by
  sorry

/-- **Exercise.** If `f` has a right-inverse, then `f` is an
epimorphism. -/
theorem Category.isEpi_of_hasRightInverse (C : Category.{u, v}) {A B : C.Obj} {f : C.Hom A B}
    (hf : ∃ g, C.comp f g = C.id B) : C.IsEpi f := by
  sorry

/-- **Exercise** (converse fails). There is a category with an
epimorphism that has no right-inverse. -/
theorem exists_isEpi_not_hasRightInverse :
    ∃ (C : Category.{u, v}) (A B : C.Obj) (f : C.Hom A B),
      C.IsEpi f ∧ ¬ ∃ g, C.comp f g = C.id B := by
  sorry

/-- **Exercise.** The composition of two monomorphisms is a
monomorphism. -/
theorem Category.isMono_comp (C : Category.{u, v}) {A B D : C.Obj} {f : C.Hom A B}
    {g : C.Hom B D} (hf : C.IsMono f) (hg : C.IsMono g) : C.IsMono (C.comp g f) := by
  sorry

/-- **Exercise.** The composition of two epimorphisms is an
epimorphism. -/
theorem Category.isEpi_comp (C : Category.{u, v}) {A B D : C.Obj} {f : C.Hom A B}
    {g : C.Hom B D} (hf : C.IsEpi f) (hg : C.IsEpi g) : C.IsEpi (C.comp g f) := by
  sorry

/-- **Exercise.** The subcategory of monomorphisms of `C`. -/
def monoSubcategory (C : Category.{u, v}) : Subcategory C where
  ObjPred _ := True
  HomPred _ _ f := C.IsMono f
  id_mem _ := by sorry
  comp_mem _ _ _ _ _ := by sorry

/-- **Exercise.** The subcategory of epimorphisms of `C`. -/
def epiSubcategory (C : Category.{u, v}) : Subcategory C where
  ObjPred _ := True
  HomPred _ _ f := C.IsEpi f
  id_mem _ := by sorry
  comp_mem _ _ _ _ _ := by sorry

end Morphisms

section UniversalProperties

universe u v

/-- `I` is initial in `C`: for every object `A`, there is exactly one
morphism `I ⟶ A`. -/
def Category.IsInitial (C : Category.{u, v}) (I : C.Obj) : Prop :=
  ∀ A : C.Obj, ∃! _ : C.Hom I A, True

/-- `F` is final (terminal) in `C`: for every object `A`, there is
exactly one morphism `A ⟶ F`. -/
def Category.IsFinal (C : Category.{u, v}) (F : C.Obj) : Prop :=
  ∀ A : C.Obj, ∃! _ : C.Hom A F, True

/-- The category from `(ℤ, ≤)` has neither an initial nor a final
object. -/
theorem not_exists_isInitial_leCategory_int : ¬ ∃ I, (leCategory ℤ).IsInitial I := by
  sorry

theorem not_exists_isFinal_leCategory_int : ¬ ∃ F, (leCategory ℤ).IsFinal F := by
  sorry

/-- By contrast, the slice category of `(ℤ, ≤)` under `3` does have a
final object (namely `(3,3)`), though it still has no initial
object. -/
theorem exists_isFinal_sliceCategory_leCategory_int :
    ∃ p, (sliceCategory (leCategory ℤ) (3 : ℤ)).IsFinal p := by
  sorry

/-- **A type is initial in the category of types iff it is empty**
(so `∅` is initial, and it is the *only* initial object up to
isomorphism). -/
theorem isInitial_typeCategory_iff {A : Type u} :
    (typeCategory).IsInitial A ↔ IsEmpty A := by
  sorry

/-- Every singleton type is final in the category of types; final
objects are in particular not unique. -/
theorem isFinal_typeCategory_unit : (typeCategory).IsFinal PUnit := by
  sorry

/-- **Initial objects are unique up to a unique isomorphism.** -/
theorem Category.isIso_of_isInitial_isInitial (C : Category.{u, v}) {I1 I2 : C.Obj}
    (h1 : C.IsInitial I1) (h2 : C.IsInitial I2) : ∃! f : C.Hom I1 I2, C.IsIso f := by
  sorry

/-- **Final objects are unique up to a unique isomorphism.** -/
theorem Category.isIso_of_isFinal_isFinal (C : Category.{u, v}) {F1 F2 : C.Obj}
    (h1 : C.IsFinal F1) (h2 : C.IsFinal F2) : ∃! f : C.Hom F1 F2, C.IsIso f := by
  sorry

/-- The category of maps out of `A` respecting an equivalence
relation `r`: objects are pairs `(Z, φ : A → Z)` with `φ` constant on
`r`-classes. -/
def quotientMapCategory {A : Type u} (r : Setoid A) : Category.{u + 1, u} where
  Obj := {p : Σ Z : Type u, A → Z // ∀ a1 a2, r.r a1 a2 → p.2 a1 = p.2 a2}
  Hom X Y := {σ : X.1.1 → Y.1.1 // σ ∘ X.1.2 = Y.1.2}
  id X := ⟨id, by sorry⟩
  comp g f := ⟨g.1 ∘ f.1, by sorry⟩
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **The quotient satisfies a universal property**: `(π, A/r)` is
initial in `quotientMapCategory r`. -/
theorem isInitial_quotientMapCategory {A : Type u} (r : Setoid A) :
    (quotientMapCategory r).IsInitial ⟨⟨Quotient r, fun a => ⟦a⟧⟩, by sorry⟩ := by
  sorry

/-- A category **has (binary) products** if `twoLegCategory C A B`
has a final object, for every `A`, `B`. -/
def Category.HasProducts (C : Category.{u, v}) : Prop :=
  ∀ A B : C.Obj, ∃ p, (twoLegCategory C A B).IsFinal p

/-- A category **has (binary) coproducts** if `twoLegCoCategory C A B`
has an initial object, for every `A`, `B`. -/
def Category.HasCoproducts (C : Category.{u, v}) : Prop :=
  ∀ A B : C.Obj, ∃ p, (twoLegCoCategory C A B).IsInitial p

/-- **Products, as a universal property.** The category of types has
(binary) products: `(A × B, π_A, π_B)` is final in
`twoLegCategory typeCategory A B`. This is the same fact as "the
Cartesian product of sets satisfies the expected universal property,"
phrased via `twoLegCategory` instead of a literal commutative
diagram. -/
theorem hasProducts_typeCategory : (typeCategory).HasProducts := by
  sorry

/-- The category from `(ℤ, ≤)` has products: the product of `a` and
`b` is `min a b`. -/
theorem hasProducts_leCategory_int : (leCategory ℤ).HasProducts := by
  sorry

/-- **The disjoint union is a coproduct in the category of types.** -/
theorem hasCoproducts_typeCategory : (typeCategory).HasCoproducts := by
  sorry

/-- The category from `(ℤ, ≤)` has coproducts: the coproduct of `a`
and `b` is `max a b`. -/
theorem hasCoproducts_leCategory_int : (leCategory ℤ).HasCoproducts := by
  sorry

/-- **Exercise.** A final object in `C` is initial in the opposite
category `C^op`. -/
theorem Category.isInitial_op_of_isFinal (C : Category.{u, v}) {F : C.Obj} (h : C.IsFinal F) :
    C.op.IsInitial F := by
  sorry

/-- **Exercise.** The one-point pointed set is both initial and final
in the category of pointed sets. -/
theorem isInitial_and_isFinal_pointedSetCategory :
    (pointedSetCategory).IsInitial (⟨PUnit, id⟩ : pointedSetCategory.Obj) ∧
      (pointedSetCategory).IsFinal (⟨PUnit, id⟩ : pointedSetCategory.Obj) := by
  sorry

/-- The category from `(ℕ+, ∣)`. -/
def divCategory : Category.{0, 0} :=
  preorderCategory (S := ℕ+) (r := (· ∣ ·)) (by sorry) (by sorry)

/-- **Exercise.** `divCategory` has products (given by `gcd`) and
coproducts (given by `lcm`). -/
theorem hasProducts_divCategory : divCategory.HasProducts := by
  sorry

theorem hasCoproducts_divCategory : divCategory.HasCoproducts := by
  sorry

/-- **Exercise.** In any category, `A × B ≅ B × A`, if both products
exist. -/
theorem objIso_prod_comm (C : Category.{u, v}) {A B : C.Obj}
    {p : (twoLegCategory C A B).Obj} (hp : (twoLegCategory C A B).IsFinal p)
    {q : (twoLegCategory C B A).Obj} (hq : (twoLegCategory C B A).IsFinal q) :
    C.ObjIso p.1 q.1 := by
  sorry

/-- The product equivalence relation on `A × B`, from equivalence
relations on `A` and `B`. -/
def prodSetoid {A B : Type u} (rA : Setoid A) (rB : Setoid B) : Setoid (A × B) where
  r p q := rA.r p.1 q.1 ∧ rB.r p.2 q.2
  iseqv := by sorry

/-- **Exercise.** The quotient of the product agrees with the product
of the quotients. -/
theorem quotient_prodSetoid_equiv {A B : Type u} (rA : Setoid A) (rB : Setoid B) :
    Nonempty (Quotient (prodSetoid rA rB) ≃ Quotient rA × Quotient rB) := by
  sorry

/-- **Co-fibered category.** Given a category `C` and two morphisms
`α : T ⟶ A`, `β : T ⟶ B` with common source, the category `C^{α,β}`
of commuting pairs `(f : A ⟶ Z, g : B ⟶ Z)` with `f ∘ α = g ∘ β`. -/
def coFiberedCategory (C : Category.{u, v}) {A B T : C.Obj}
    (α : C.Hom T A) (β : C.Hom T B) : Category where
  Obj := {p : Σ Z : C.Obj, C.Hom A Z × C.Hom B Z // C.comp p.2.1 α = C.comp p.2.2 β}
  Hom X Y := {σ : C.Hom X.1.1 Y.1.1 // C.comp σ X.1.2.1 = Y.1.2.1 ∧ C.comp σ X.1.2.2 = Y.1.2.2}
  id X := ⟨C.id X.1.1, by sorry, by sorry⟩
  comp g f := ⟨C.comp g.1 f.1, by sorry, by sorry⟩
  comp_assoc := by sorry
  id_comp := by sorry
  comp_id := by sorry

/-- **Fibered product**: a final object of `fiberedCategory C α β`. -/
def Category.IsFiberedProduct (C : Category.{u, v}) {A B T : C.Obj} (α : C.Hom A T)
    (β : C.Hom B T) (p : (fiberedCategory C α β).Obj) : Prop :=
  (fiberedCategory C α β).IsFinal p

/-- **Fibered coproduct**: an initial object of `coFiberedCategory C
α β`. -/
def Category.IsFiberedCoproduct (C : Category.{u, v}) {A B T : C.Obj} (α : C.Hom T A)
    (β : C.Hom T B) (p : (coFiberedCategory C α β).Obj) : Prop :=
  (coFiberedCategory C α β).IsInitial p

/-- **Exercise.** The category of types has fibered products. -/
theorem exists_isFiberedProduct_typeCategory {A B T : Type u} (α : A → T) (β : B → T) :
    ∃ p, (typeCategory).IsFiberedProduct α β p := by
  sorry

/-- **Exercise.** The category of types has fibered coproducts. -/
theorem exists_isFiberedCoproduct_typeCategory {A B T : Type u} (α : T → A) (β : T → B) :
    ∃ p, (typeCategory).IsFiberedCoproduct α β p := by
  sorry

end UniversalProperties

end Algebra0Lean.Prelims
