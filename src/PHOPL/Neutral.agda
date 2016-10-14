module PHOPL.Neutral where

open import Data.Empty renaming (⊥ to Empty) -- TODO Move to Prelims
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_) -- TODO Move to Prelims
open import Data.List
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.PathSub

data Neutral (V : Alphabet) : Set where
  var : Var V -Term → Neutral V
  app : Neutral V → Term V → Neutral V

decode-Neutral : ∀ {V} → Neutral V → Term V
decode-Neutral (var x) = var x
decode-Neutral (app M N) = appT (decode-Neutral M) N

nrep : ∀ {U} {V} → Rep U V → Neutral U → Neutral V
nrep ρ (var x) = var (ρ -Term x)
nrep ρ (app M N) = app (nrep ρ M) (N 〈 ρ 〉)

nrep-comp : ∀ {U V W ρ' ρ N} → nrep (ρ' •R ρ) N ≡ nrep ρ' (nrep ρ N)
nrep-comp {N = var x} = refl
nrep-comp {N = app N x} = {!!}

neutral-red' : ∀ {V} {N : Neutral V} {M₁} {M₂} → M₁ ↠ M₂ → decode-Neutral N ≡ M₁ →
  Σ[ N' ∈ Neutral V ] decode-Neutral N' ≡ M₂
neutral-red' {N = var _} (osr-red (redex βT)) ()
neutral-red' {N = app (var _) _} (osr-red (redex βT)) xF≡ΛMN = ⊥-elim (var-not-Λ (appT-injl xF≡ΛMN))
neutral-red' {N = app (app _ _) _} (osr-red (redex βT)) EF≡ΛMN = ⊥-elim (app-not-Λ (appT-injl EF≡ΛMN))
neutral-red' {N = var _} (osr-red (app _)) ()
neutral-red' {N = app _ _} (osr-red (app {c = -bot} _)) ()
neutral-red' {N = app _ _} (osr-red (app {c = -imp} _)) ()
neutral-red' {N = app N P} (osr-red (app {c = -appTerm} (appl {F = F ∷ []} E⇒E'))) NP≡EF = 
  let (N' ,p N'≡E') = neutral-red' (osr-red E⇒E') (appT-injl NP≡EF) in
  app N' P ,p cong₂ appT N'≡E' (appT-injr NP≡EF)
neutral-red' {N = app N P} (osr-red (app {c = -appTerm} (appr (appl {E' = F'} {F = []} F↠F')))) NP≡EF = app N F' ,p cong (λ x → appT x F') (appT-injl NP≡EF)
neutral-red' {N = app _ _} (osr-red (app {c = -appTerm} (appr (appr ())))) _
neutral-red' {N = app _ _} (osr-red (app {c = -lamTerm x} _)) ()
neutral-red' {N = N} ref N≡M₁ = N ,p N≡M₁
neutral-red' (trans-red M₁↠M₂ M₂↠M₃) N≡M₁ = 
  let (_ ,p N₂≡M₂) = neutral-red' M₁↠M₂ N≡M₁ in
  neutral-red' M₂↠M₃ N₂≡M₂

neutral-red : ∀ {V} {N : Neutral V} {M} → decode-Neutral N ↠ M →
  Σ[ N' ∈ Neutral V ] decode-Neutral N' ≡ M
neutral-red N↠M = neutral-red' N↠M refl
