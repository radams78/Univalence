\begin{code}
module PHOPL.KeyRedex where

open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Red

data key-redex {V} : ∀ {K} → Expression V K → Expression V K → Set where
  βTkr : ∀ {A} {M} {N : Term V} → SN M → key-redex (appT (ΛT A M) N) (M ⟦ x₀:= N ⟧)
  βPkr : ∀ {φ : Term V} {δ ε} (SNφ : SN φ) (SNε : SN ε) → key-redex (appP (ΛP φ δ) ε) (δ ⟦ x₀:= ε ⟧)
  βEkr : ∀ {N N' : Term V} {A} {P} {Q} (SNN : SN N) (SNN' : SN N') (SNQ : SN Q) →
           key-redex (app* N N' (λλλ A P) Q) (P ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧)
  appTkr : ∀ {M N P : Term V} → key-redex M N → key-redex (appT M P) (appT N P)

postulate key-redex-confluent : ∀ {V} {K} {M N P : Expression V K} →
                              key-redex M N → M ⇒ P → Σ[ Q ∈ Expression V K ] key-redex P Q × N ↠⁺ Q

key-redex-SN : ∀ {V} {K} {M N : Expression V K} → SN N → key-redex M N → SN M
key-redex-SN {M = M} {N} SNN = SNE (λ N → ∀ {M} → key-redex M N → SN M) 
  (λ {N} SNN ih {M} M▷N → SNI M (λ M' M⇒M' → 
    let (P ,p M'▷P ,p N↠⁺P) = key-redex-confluent M▷N M⇒M' in 
      ih P N↠⁺P M'▷P)) 
  SNN

key-redex-rep : ∀ {U} {V} {K} {M N : Expression U K} {ρ : Rep U V} →
  key-redex M N → key-redex (M 〈 ρ 〉) (N 〈 ρ 〉)
key-redex-rep {ρ = ρ} (βTkr {A} {M} {N} SNM) = 
  subst (key-redex (appT (ΛT A M) N 〈 ρ 〉)) (sym (compRS-botsub M)) 
    (βTkr (SNrep R-creates-rep SNM))
key-redex-rep {ρ = ρ} (βPkr {φ} {δ} {ε} SNφ SNε) = 
  subst (key-redex ((appP (ΛP φ δ) ε) 〈 ρ 〉)) (sym (compRS-botsub δ)) 
    (βPkr (SNrep R-creates-rep SNφ) (SNrep R-creates-rep SNε))
key-redex-rep {ρ = ρ} (βEkr {N} {N'} {A} {P} {Q} SNN SNN' SNQ) = 
  subst (key-redex (app* N N' (λλλ A P) Q 〈 ρ 〉)) (botsub₃-Rep↑₃ P)
    (βEkr (SNrep R-creates-rep SNN) (SNrep R-creates-rep SNN') (SNrep R-creates-rep SNQ))
key-redex-rep {ρ = ρ} (appTkr M▷N) = appTkr (key-redex-rep M▷N)
--REFACTOR Common pattern

postulate key-redex-red : ∀ {V} {K} {M N : Expression V K} → key-redex M N → M ↠ N

postulate key-redex-⋆ : ∀ {V} {M M' N N' : Term V} {P} →
                        key-redex M M' → key-redex (M ⋆[ P ∶ N ∼ N' ]) (M' ⋆[ P ∶ N ∼ N' ])
\end{code}
