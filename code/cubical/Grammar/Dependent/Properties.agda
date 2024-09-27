open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Dependent.Properties (Alphabet : hSet ℓ-zero) where

open import Cubical.Data.Sigma
open import Cubical.Data.FinSet

open import Cubical.Foundations.Structure

open import Grammar.Base Alphabet
open import Grammar.Properties Alphabet
open import Grammar.Dependent.Base Alphabet
open import Grammar.Top Alphabet
open import Term.Base Alphabet
open import Grammar.Literal Alphabet

private
  variable
    ℓg ℓh ℓS : Level

module _
  {A : Type ℓS} {h : A → Grammar ℓh}
  {isSetA : isSet A}
  (isFinSetAlphabet : isFinSet ⟨ Alphabet ⟩)
  where

  isMono-LinΣ-intro : (a : A) → isMono (LinΣ-intro {h = h} a)
  isMono-LinΣ-intro a e e' !∘e=!∘e' =
    funExt λ w → funExt λ p →
      sym (transportRefl (e w p)) ∙
      Σ-contractFst (refl , (isSetA _ _ _)) .fst
        (PathΣ→ΣPathTransport _ _ (funExt⁻ (funExt⁻ !∘e=!∘e' w) p))

  unambiguous'Σ :
    unambiguous' (LinΣ[ a ∈ A ] h a) →
      (a : A)  → unambiguous' (h a)
  unambiguous'Σ unambigΣ a f f' !≡ =
    isMono-LinΣ-intro a f f'
      (unambigΣ (LinΣ-intro a ∘g f) (LinΣ-intro a ∘g f')
        -- Need to change the endpoints of !≡ to line up with the
        -- ⊤-intro at the proper domain
        (unambiguous⊤ _ _ ∙ !≡ ∙ sym (unambiguous⊤ _ _)))