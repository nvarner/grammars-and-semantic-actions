open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

module Grammar.Lift (Alphabet : hSet ℓ-zero) where

open import Grammar.Base Alphabet
open import Term.Base Alphabet

Lift-intro :
  ∀ {ℓG ℓG'} {g : Grammar ℓG} →
  g ⊢ LiftGrammar {ℓG} {ℓG'} g
Lift-intro = λ w z → lift z

Lift-elim :
  ∀ {ℓG ℓG'} {g : Grammar ℓG} →
  LiftGrammar {ℓG} {ℓG'} g ⊢ g
Lift-elim = λ w (lift x) → x

