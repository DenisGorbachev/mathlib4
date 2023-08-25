/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Computability.Language

/-!
# Context-Free Grammar

This file contains the definition of a Context-Free Grammar (CFG), which is a grammar that has a
single nonterminal symbol on the left-hand side of each rule.
Derivation by a grammar is inherently nondeterministic.
-/

universe u

/--
The type of symbols is the disjoint union of terminals `T` and nonterminals `N`.
-/
inductive Symbol (T : Type u) (N : Type u)
  | terminal    (t : T) : Symbol T N
  | nonterminal (n : N) : Symbol T N

/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CFG (T : Type u) where
  NT : Type u                            -- type of nonterminals
  initial : NT                           -- initial nonterminal
  rules : List (NT × List (Symbol T NT)) -- rewrite rules

namespace CFG

variable {T : Type u}

/-- One step of context-free transformation. -/
def Transforms (g : CFG T) (w₁ w₂ : List (Symbol T g.NT)) : Prop :=
  ∃ r : g.NT × List (Symbol T g.NT),
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.NT),
      w₁ = u ++ [Symbol.nonterminal r.fst] ++ v ∧ w₂ = u ++ r.snd ++ v

/-- Any number of steps of context-free transformation. -/
def Derives (g : CFG T) : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def Generates (g : CFG T) (w : List T) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w)

/-- The set of words that can be derived from the initial nonterminal. -/
def language (g : CFG T) : Language T :=
  setOf g.Generates

/-- Predicate "[language] is context-free"; defined by existence of a context-free grammar. -/
def _root_.Language.IsCF (L : Language T) : Prop :=
  ∃ g : CFG T, g.language = L

variable {g : CFG T}

lemma Transforms.single {v w : List (Symbol T g.NT)} (hvw : g.Transforms v w) :
    g.Derives v w :=
  Relation.ReflTransGen.single hvw

@[refl]
lemma Derives.refl {w : List (Symbol T g.NT)} :
    g.Derives w w :=
  Relation.ReflTransGen.refl

@[trans]
lemma Derives.derives {u v w : List (Symbol T g.NT)}
    (huv : g.Derives u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  Relation.ReflTransGen.trans huv hvw

lemma Derives.transforms {u v w : List (Symbol T g.NT)}
    (huv : g.Derives u v) (hvw : g.Transforms v w) :
    g.Derives u w :=
  huv.derives hvw.single

lemma Transforms.derives {u v w : List (Symbol T g.NT)}
    (huv : g.Transforms u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  huv.single.derives hvw

lemma Derives.eq_or_head {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Transforms u v ∧ g.Derives v w :=
  Relation.ReflTransGen.cases_head huw

lemma Derives.eq_or_tail {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Derives u v ∧ g.Transforms v w :=
  (Relation.ReflTransGen.cases_tail huw).casesOn (Or.inl ∘ Eq.symm) Or.inr
