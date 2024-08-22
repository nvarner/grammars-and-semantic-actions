open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Semantics.Grammar.Dependent ((Σ₀ , isSetΣ₀) : hSet ℓ-zero) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv renaming (_∙ₑ_ to _⋆_)

open import Cubical.Data.List
open import Cubical.Data.Sum
open import Cubical.Data.W.Indexed
open import Cubical.Data.Unit
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.SumFin hiding (fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.FinSet
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Nullary.Base
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary.DecidablePropositions

open import Cubical.HITs.PropositionalTruncation as PT

open import Semantics.Helper
open import Semantics.Grammar.Base (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.Literal (Σ₀ , isSetΣ₀)
open import Semantics.Grammar.KleeneStar (Σ₀ , isSetΣ₀)

private
  variable
    ℓG ℓS : Level

LinearΠ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΠ {A = A} f w = ∀ (a : A) → f a w

LinearΣ : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ {A = A} f w = Σ[ a ∈ A ] f a w

LinearΣ-syntax : {A : Type ℓS} → (A → Grammar ℓG) → Grammar (ℓ-max ℓS ℓG)
LinearΣ-syntax = LinearΣ

syntax LinearΣ-syntax {A} (λ x → B) = LinΣ[ x ∈ A ] B

⊕Σ₀ : Grammar ℓ-zero
⊕Σ₀ = LinearΣ λ (c : Σ₀) → literal c

String→KL* : (w : String) → KL* ⊕Σ₀ w
String→KL* [] = nil refl
String→KL* (x ∷ w) =
  cons ((([ x ] , w) , refl) , (((x , refl)) , (String→KL* w)))
