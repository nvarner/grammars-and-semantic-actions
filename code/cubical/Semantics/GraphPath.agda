{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
module Semantics.GraphPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Function.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Functions.Embedding

open import Cubical.Data.Empty as ⊥ hiding (elim ; rec)
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.FinData.More using (DecΣ)
open import Cubical.Data.FinSet

open import Cubical.HITs.PropositionalTruncation as PT hiding (elim ; rec ; map)

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties

private
  variable
    ℓ ℓ' : Level
    n : ℕ

record directedGraph : Type (ℓ-suc ℓ) where
  field
    states : FinSet ℓ
    directed-edges : FinSet ℓ
    src : ⟨ directed-edges ⟩ → ⟨ states ⟩
    dst : ⟨ directed-edges ⟩ → ⟨ states ⟩

  record GraphWalk (length : ℕ) : Type ℓ where
    field
      vertices : Fin (suc length) → ⟨ states ⟩
      edges : Fin length → ⟨ directed-edges ⟩
      compat-src : (i : Fin length) → src (edges i) ≡ vertices (weakenFin i)
      compat-dst : (i : Fin length) → dst (edges i) ≡ vertices (suc i)

    start : ⟨ states ⟩
    start = vertices zero

    end : ⟨ states ⟩
    end = vertices (fromℕ length)

  open GraphWalk

  trivial : ⟨ states ⟩ → GraphWalk 0
  trivial v .vertices k = v
  trivial v .edges ()
  trivial v .compat-src ()
  trivial v .compat-dst ()

  tailGW : GraphWalk (suc n) → GraphWalk n
  tailGW gw .vertices = gw .vertices ∘ suc
  tailGW gw .edges = gw .edges ∘ suc
  tailGW gw .compat-src = gw .compat-src ∘ suc
  tailGW gw .compat-dst = gw .compat-dst ∘ suc

  consGW : (e : ⟨ directed-edges ⟩) (gw : GraphWalk n) → dst e ≡ start gw → GraphWalk (suc n)
  consGW e gw p .vertices zero = src e
  consGW e gw p .vertices (suc k) = gw .vertices k
  consGW e gw p .edges zero = e
  consGW e gw p .edges (suc k) = gw .edges k
  consGW e gw p .compat-src zero = refl
  consGW e gw p .compat-src (suc k) = gw .compat-src k
  consGW e gw p .compat-dst zero = p
  consGW e gw p .compat-dst (suc k) = gw .compat-dst k

  drop : (gw : GraphWalk n) → (k : Fin (suc n)) → Σ[ m ∈ ℕ ] Σ[ gw' ∈ GraphWalk m ] (gw .vertices k ≡ start gw') × (end gw ≡ end gw')
  drop gw zero = _ , gw , refl , refl
  drop {suc n} gw (suc k) = drop (tailGW gw) k

  hasUniqueVertices : GraphWalk n → Type _
  hasUniqueVertices gw = isEmbedding (gw .vertices)

  makeUnique : (gw : GraphWalk n) → Σ[ m ∈ ℕ ] Σ[ gw' ∈ GraphWalk m ] hasUniqueVertices gw' × (start gw ≡ start gw') × (end gw ≡ end gw')
  makeUnique {zero} gw = {!!}
  makeUnique {suc n} gw =
    let newVert = gw .vertices zero in
    let newEdge = gw .edges zero in
    let n' , gw' , unique , startAgree , endAgree = makeUnique (tailGW gw) in
    DecΣ _ (λ k → gw' .vertices k ≡ newVert) (λ k → isFinSet→Discrete (str states) _ newVert) & decRec
      (λ (k , p) →
        let n'' , gw'' , startAgree' , endAgree' = drop gw' k in
        n'' , gw'' , {!!} , sym p ∙ startAgree' , endAgree ∙ endAgree')
      (λ ¬ΣnewVert →
        let gw'' = consGW newEdge gw' (gw .compat-dst zero ∙ startAgree) in
        let uniqueGW'' : hasUniqueVertices gw''
            uniqueGW'' = {!!} in
        _ , gw'' , uniqueGW'' , (sym $ gw .compat-src zero) , endAgree)

