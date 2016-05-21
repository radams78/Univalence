module PHOPL.Neutral where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.PathSub

data Neutral (V : Alphabet) : VarKind → Set
data Nf : Alphabet → VarKind → Set

data Neutral V where
  var    : ∀ K → Var V K → Neutral V K
  appTn  : Neutral V -Term → Nf V -Term → Neutral V -Term
  appPn  : Neutral V -Proof → Nf V -Proof → Neutral V -Proof
  plusn  : Neutral V -Path → Neutral V -Proof
  minusn : Neutral V -Path → Neutral V -Proof
  _⊃*l_  : Neutral V -Path → Nf V -Path → Neutral V -Path
  _⊃*r_  : Nf V -Path → Neutral V -Path → Neutral V -Path
  app*n  : Nf V -Term → Nf V -Term → Neutral V -Path → Nf V -Path → Neutral V -Path

data Nf  where
  neutral : ∀ {V} {K} → Neutral V K → Nf V K
  ⊥nf   : ∀ {V} → Nf V -Term
  _⊃nf_ : ∀ {V} → Nf V -Term → Nf V -Term → Nf V -Term
  ΛTnf  : ∀ {V} → Type → Nf (V , -Term) -Term → Nf V -Term
  ΛPnf  : ∀ {V} → Nf V -Term → Nf (V , -Proof) -Proof → Nf V -Proof
  refnf : ∀ {V} → Nf V -Term → Nf V -Path
  univnf : ∀ {V} → Nf V -Term → Nf V -Term → Nf V -Proof → Nf V -Proof → Nf V -Path
  λλλnf  : ∀ {V} → Type → Nf (V , -Term , -Term , -Path) -Path → Nf V -Path

decode : ∀ {V} {K} → Neutral V K → Expression V (varKind K)
decodenf : ∀ {V} {K} → Nf V K → Expression V (varKind K)

decode (var K x) = var x
decode (appTn E F) = appT (decode E) (decodenf F)
decode (appPn E F) = appP (decode E) (decodenf F)
decode (plusn E) = plus (decode E)
decode (minusn E) = minus (decode E)
decode (E ⊃*l F) = decode E ⊃* decodenf F
decode (E ⊃*r F) = decodenf E ⊃* decode F
decode (app*n E₁ E₂ E₃ E₄) = app* (decodenf E₁) (decodenf E₂) (decode E₃) (decodenf E₄)

decodenf (neutral E) = decode E
decodenf ⊥nf = ⊥
decodenf (E ⊃nf F) = decodenf E ⊃ decodenf F
decodenf (ΛTnf A E) = ΛT A (decodenf E)
decodenf (ΛPnf E F) = ΛP (decodenf E) (decodenf F)
decodenf (refnf E) = reff (decodenf E)
decodenf (univnf E₁ E₂ E₃ E₄) = univ (decodenf E₁) (decodenf E₂) (decodenf E₃) (decodenf E₄)
decodenf (λλλnf A E) = λλλ A (decodenf E)


