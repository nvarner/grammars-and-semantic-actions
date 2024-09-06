open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module DFA.Decider (Alphabet : hSet ℓ-zero) where

open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.Data.FinSet
open import Cubical.Data.Bool
open import Cubical.Data.Sum
open import Cubical.Data.SumFin
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.List hiding (init)

open import Grammar Alphabet
open import Grammar.Equivalence Alphabet
open import Grammar.KleeneStar Alphabet
open import Term Alphabet
open import DFA.Base Alphabet
open import Helper

private
  variable ℓΣ₀ ℓD ℓP ℓ : Level

module _ (D : DFA {ℓD}) where
  open DFA D

  open *l-Algebra
  open Algebra
  open AlgebraHom

  module _ (q-start : ⟨ Q ⟩) where
    -- The decider leverages the function TraceAppendLiteral
    -- which turns the Trace into a SnocTrace, snoc's it, and
    -- then turns the resulting SnocTrace back into a trace.
    --
    -- This feels like an unsatisfactory definition but there does not
    -- seem to be a nicer way to do this, other than taking SnocTrace as the
    -- primitive notion of trace. However, this would sacrifice nice
    -- definitional harmony with existing Brzozowski derivative
    -- actions on DFAs, AND would lose harmony with the NFA definitions
    ExtendTraceFrom : (c : ⟨ Alphabet ⟩) →
      TraceFrom q-start ⊗ (literal c) ⊢ TraceFrom q-start
    ExtendTraceFrom c _ (s , (q , trace), lit) =
      (δ q c) ,
      TraceAppendLiteral q-start q c _ (s , (trace , lit))

    RunFromState : string-grammar ⊢ TraceFrom q-start
    RunFromState = foldKL*l char the-alg
      where
      the-alg : *l-Algebra char
      the-alg .the-ℓ = ℓD
      the-alg .G = TraceFrom q-start
      the-alg .nil-case w pε = q-start , (nil _ pε)
      the-alg .snoc-case w (s , trFrom , (c , lit)) =
        ExtendTraceFrom c w (s , (trFrom , lit))

    DecideFromState : String → Bool
    DecideFromState w =
      let (q-end , trace) = RunFromState _ ⌈ w ⌉ in
      decRec
        (λ acc → true)
        (λ ¬acc → false)
        (isAcc q-end .snd)

  Decide : String → Bool
  Decide = DecideFromState init

