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

/-!
# Chapter I: Preliminaries — Set theory and categories

Selected results from Aluffi, *Algebra: Chapter 0*, §I.1 (Naive set
theory) and §I.2 (Functions between sets).
-/

namespace Algebra0Lean.Prelims

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
  sorry

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
theorem equivalence_modZRelation : Equivalence modZRelation := by
  sorry

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
  sorry

/-- **A function really "is" its graph.** `graphOf` is a bijection
between functions `X → Y` and subsets of `X × Y` satisfying
`IsGraph`. -/
theorem bijective_graphOf :
    Function.Bijective (fun f : X → Y =>
      (⟨graphOf f, isGraph_graphOf f⟩ : {Γ : Set (X × Y) // IsGraph Γ})) := by
  sorry

/-- Composition of functions is associative. -/
theorem comp_assoc {Z W : Type*} (f : X → Y) (g : Y → Z) (h : Z → W) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  sorry

/-- The identity function is a left unit for composition. -/
theorem id_comp (f : X → Y) : (id : Y → Y) ∘ f = f := by
  sorry

/-- The identity function is a right unit for composition. -/
theorem comp_id (f : X → Y) : f ∘ (id : X → X) = f := by
  sorry

/-- Two types are isomorphic if there is a bijection between them. -/
def Isomorphic (A B : Type*) : Prop := Nonempty (A ≃ B)

/-- The identity function is a bijection. -/
theorem bijective_id : Function.Bijective (id : X → X) := by
  sorry

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
  sorry

/-- For a bijective `f` with two-sided inverse `g`, the forward image
under `g` of a subset agrees with the preimage under `f`. -/
theorem image_inverse_eq_preimage {f : X → Y} {g : Y → X}
    (hgl : Function.LeftInverse g f) (hgr : Function.RightInverse g f) (T : Set Y) :
    g '' T = f ⁻¹' T := by
  sorry

/-- **Exercise I.2.3** (first part). The inverse of a bijection is a
bijection. -/
theorem bijective_invFun [Nonempty X] {f : X → Y} (hf : Function.Bijective f) :
    Function.Bijective (Function.invFun f) := by
  sorry

/-- **Exercise I.2.3** (second part). The composite of two bijections
is a bijection. -/
theorem bijective_comp {Z : Type*} {f : X → Y} {g : Y → Z}
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (g ∘ f) := by
  sorry

/-- **Exercise I.2.4** (first part). Isomorphism of sets is
reflexive, symmetric, and transitive. -/
theorem isomorphic_refl (A : Type*) : Isomorphic A A := by
  sorry

theorem isomorphic_symm {A B : Type*} (h : Isomorphic A B) : Isomorphic B A := by
  sorry

theorem isomorphic_trans {A B C : Type*} (h1 : Isomorphic A B) (h2 : Isomorphic B C) :
    Isomorphic A C := by
  sorry

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

end Algebra0Lean.Prelims
