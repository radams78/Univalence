module PHOPL.Neutral where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.PathSub

data Neutral {V} : Term V → Set where
  var : ∀ (x : Var V -Term) → Neutral (var x)
  app : ∀ {M N : Term V} → Neutral M → SN N → Neutral (appT M N)

Neutral-rep : ∀ {U} {V} (M : Term U) (ρ : Rep U V) → Neutral M → Neutral (M 〈 ρ 〉)
Neutral-rep .(var x) ρ (var x) = var (ρ _ x)
Neutral-rep {U} {V} .(appT M N) ρ (app {M} {N} M-neutral N-SN) = 
  app (Neutral-rep {U} {V} M ρ M-neutral) (SNrep R-creates-rep N-SN)

Neutral-SN-aux : ∀ {V} {M : Term V} {NN} → Neutral M → all-SN NN → SN (APP M NN)
Neutral-SN-aux (var x) NN-SN = var-APP-SN x _ NN-SN
Neutral-SN-aux (app M-neutral N-SN) NN-SN = Neutral-SN-aux {NN = _ ∷ _} M-neutral (N-SN ,p NN-SN)

Neutral-SN : ∀ {V} {M : Term V} → Neutral M → SN M
Neutral-SN (var x) = SNvar x
Neutral-SN (app M-neutral N-SN) = Neutral-SN-aux {NN = [ _ ]} M-neutral (N-SN ,p tt)

data NeutralE {V} : Path V → Set where
  refvar : ∀ (x : Var V -Term) → NeutralE (reff (var x))
  app    : ∀ {N} {N'} {P Q : Path V} → NeutralE P → SN N → SN N' → SN Q → NeutralE (app* N N' P Q)

postulate Neutral-⋆ : ∀ {V} {M : Term V} {P} {N} {N'} → Neutral M → SN P → SN N → SN N' →
                    NeutralE (M ⋆[ P ∶ N ∼ N' ])
