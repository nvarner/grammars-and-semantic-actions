{-# OPTIONS -WnoUnsupportedIndexedMatch --lossy-unification #-}
module Semantics.NFA.Determinization where

open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure
open import Cubical.Functions.Embedding
open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions
open import Cubical.Data.List hiding (init)
open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.DecidablePredicate
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Bool hiding (_⊕_)
open import Cubical.Data.W.Indexed
open import Cubical.Data.Maybe
open import Cubical.Data.FinSet.Constructors
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order.Recursive as Ord
open import Cubical.Data.SumFin
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Grammar
open import Semantics.DFA
open import Semantics.NFA.Base
open import Semantics.Helper
open import Semantics.Term
open import Semantics.String
open import Graph.Reachability

private
  variable ℓΣ₀ ℓN ℓN' ℓP ℓ : Level

open NFADefs

module _ {ℓN}
  ((Σ₀ , isFinSetΣ₀) : FinSet ℓ-zero)
  (N : NFA ℓN Σ₀) where
  open NFA
  private module N = NFA N

  -- The NFA without labelled transitions, viewed as a directed graph
  open directedGraph
  ε-graph : directedGraph
  states ε-graph = N .Q
  directed-edges ε-graph = N .ε-transition
  src ε-graph = N .ε-src
  dst ε-graph = N .ε-dst

  -- The decidable finite set of states reachable from q-start
  ε-reach : N .Q .fst → FinSetDecℙ (N .Q) .fst
  fst (fst (ε-reach q-start q-end)) = _
  snd (fst (ε-reach q-start q-end)) = isPropPropTrunc
  snd (ε-reach q-start q-end) = DecReachable ε-graph q-start q-end

  -- TODO: perhaps prove this is a closure, i.e. that the function is idempotent
  ε-closure : ⟨ FinSetDecℙ N.Q ⟩ → ⟨ FinSetDecℙ N.Q ⟩
  ε-closure X = FinSetDecℙ∃ N.Q N.Q X ε-reach

  δFunN : ⟨ N .Q ⟩ → Σ₀ → ⟨ FinSetDecℙ (N .Q) ⟩
  δFunN = N.hasTransition (isFinSet→Discrete isFinSetΣ₀)

  open DFADefs
  open DFA
  open Iso
  ℙDFA : DFA (ℓ-suc ℓN) (Σ₀ , isFinSetΣ₀)
  Q ℙDFA = FinSetDecℙ (N .Q)
  init ℙDFA = ε-reach (N .init)
  isAcc ℙDFA X =
    DecProp∃
      -- Quantifying over states in X : Σ[ q ∈ N .Q .fst ] X q .fst
      (Decℙ→FinSet (N .Q) X)
      -- Is any state in X accepting?
      (λ x → LiftDecProp (N .isAcc (x .fst)))
  δ ℙDFA X c = ε-closure (FinSetDecℙ∃ N.Q N.Q (ε-closure X) (flip δFunN c))

