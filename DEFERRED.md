# Deferred decisions

Open design questions for the formalization, parked here instead of being
decided on the spot. Each entry should have enough context to pick back up
later without re-deriving it from scratch.

## Disjoint union representation

**Question:** How should "disjoint union of two sets" (Aluffi §I.1,
`subsec:prelims:disjoint-unions-products`) be represented in Lean?

**Context:** The book constructs `A ⊔ B` concretely as
`({0} × A) ∪ ({1} × B)` inside an ambient set, then shows the two tagged
copies are isomorphic to `A` and `B`. Lean's `Sum` type (`α ⊕ β`, defined in
core `Init/Core.lean`) is the native equivalent — it tags elements via
`Sum.inl`/`Sum.inr` instead of `0`/`1`, and Mathlib's
`Equiv.Set.rangeInl`/`rangeInr` (`Mathlib/Logic/Equiv/Set.lean`) already give
the "tagged copy is isomorphic to the original" fact for free. There's also
`Finset.disjSum`/`Multiset.disjSum` for the finite-collection version, built
the same way on top of `Sum`.

The open question is which level to formalize at: define our own
`X ⊔ B`-style construction matching the book's literal set-builder
definition (closer to the text, but reinventing what `Sum` already gives),
or state everything directly in terms of `α ⊕ β` and cite Mathlib's
existing lemmas (idiomatic Lean, but a bigger conceptual jump from the
book's phrasing for a reader following along). Not yet decided.

**Status:** Deferred — no blueprint or Lean content added yet for this
subsection.

## Resolved: Category structure representation

**Question:** For Aluffi §I.3 (Categories), define our own `Category`
structure matching the book, or build on Mathlib's `CategoryTheory.Category`?

**Decision (2026-07-14):** Our own structure, in `Algebra0Lean.Prelims`:
objects as a `Type u`, morphisms as `Hom : Obj → Obj → Type v` (independent
universe), `id`, `comp` (argument order `(g, f) ↦ g ∘ f`, matching the
book's `gf` notation and `Function.comp`), and `comp_assoc`/`id_comp`/
`comp_id` axioms. `comp_assoc` is stated via a new shared `Associative`
predicate general enough to also restate the earlier plain-function
`comp_assoc` theorem (`I := Type*`, `Hom A B := A → B`,
`comp := Function.comp`) — the two are literally the same shape.

**Why:** Consistent with the established "own defs during the pedagogical
Prelims phase, transition to Mathlib later" convention. See
`style_own_defs_before_mathlib` in Claude's memory for this project.

**Status:** Implemented. `Category`, `IsSmall`, `End`, and ~10 category
examples (`typeCategory`, `preorderCategory`, `sliceCategory`, etc.) are in
`Prelims.lean`, all axioms still `sorry`. If/when the project actually
switches to Mathlib's `CategoryTheory` in a later chapter, this struct and
everything built on it (Morphisms, Universal properties sections) will need
a bridging pass.
