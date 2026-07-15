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
