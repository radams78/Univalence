open import Grammar.Taxonomy public
open import Grammar.Base public

module Grammar (G : Grammar) where
open Grammar G public
open import Grammar.OpFamily G public
open import Grammar.Replacement G public
open import Grammar.Replacement.SetFunctor G public
open import Grammar.Substitution G public
open import Grammar.Context G public
