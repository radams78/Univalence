\AgdaHide{
\begin{code}
module PHOPL.Computable.Meaning where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Product
open import Data.List
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red hiding (nf-is-nf)
\end{code}
}

A term is \emph{neutral} iff it has the form $x M_1 \cdots M_n$.
\begin{code}
data Neutral (V : Alphabet) : Set where
  var : Var V -Term → Neutral V
  app : Neutral V → Term V → Neutral V

nAPP : ∀ {V} → Neutral V → snocList (Term V) → Neutral V
nAPP M [] = M
nAPP M (NN snoc N) = app (nAPP M NN) N

nrep : ∀ {U V} → Neutral U → Rep U V → Neutral V
nrep (var x) ρ = var (ρ -Term x)
nrep (app M N) ρ = app (nrep M ρ) (N 〈 ρ 〉)

nrep-id : ∀ {V} {N : Neutral V} → nrep N (idRep V) ≡ N
nrep-id {N = var _} = refl
nrep-id {N = app N M} = cong₂ app nrep-id rep-idRep

nrep-comp : ∀ {U V W} {N : Neutral U} {ρ' : Rep V W} {ρ : Rep U V} → nrep N (ρ' •R ρ) ≡ nrep (nrep N ρ) ρ'
nrep-comp {N = var x} = refl
nrep-comp {N = app N N'} = cong₂ app nrep-comp (rep-comp N')

decode-Neutral : ∀ {V} → Neutral V → Term V
decode-Neutral (var x) = var x
decode-Neutral (app M N) = appT (decode-Neutral M) N

decode-Neutral-nAPP : ∀ {V} {M : Neutral V} {NN : snocList (Term V)} →
  decode-Neutral (nAPP M NN) ≡ APPl (decode-Neutral M) NN
decode-Neutral-nAPP {NN = []} = refl
decode-Neutral-nAPP {NN = NN snoc N} = cong (λ x → appT x N) (decode-Neutral-nAPP {NN = NN})

decode-Neutral-rep : ∀ {U V} {N : Neutral U} {ρ : Rep U V} → decode-Neutral (nrep N ρ) ≡ decode-Neutral N 〈 ρ 〉
decode-Neutral-rep {N = var _} = refl
decode-Neutral-rep {N = app _ M} {ρ} = cong₂ appT decode-Neutral-rep refl
\end{code}

Let us say that a term is \emph{meaningful} iff it is neutral, or $\bot$, or of the form $\phi \supset \psi$ where $\phi$ and $\psi$ are meaningful.  Given a proposition $\phi$, we will have that $E_\Gamma(\phi)$ is defined if and only if $\phi$ reduces to a meaningful proposition.

Note that (using Generation) a normal form of type $\Omega$ is meaningful.

\AgdaHide{
\begin{code}
data Meaning₀ (V : Alphabet) : Set where
  neutral : Neutral V → Meaning₀ V
  bot : Meaning₀ V

nf₀rep : ∀ {U V} → Meaning₀ U → Rep U V → Meaning₀ V
nf₀rep (neutral N) ρ = neutral (nrep N ρ)
nf₀rep bot _ = bot

data MeaningShape : Set where
  nf₀ : MeaningShape
  _imp_ : MeaningShape → MeaningShape → MeaningShape

domS : MeaningShape → List MeaningShape
domS nf₀ = []
domS (S imp T) = S ∷ domS T

data Meaning (V : Alphabet) : MeaningShape → Set where
  nf₀ : Meaning₀ V → Meaning V nf₀
  _imp_ : ∀ {S} {T} → Meaning V S → Meaning V T → Meaning V (S imp T)

nfrep : ∀ {U} {V} {S} → Meaning U S → Rep U V → Meaning V S
nfrep (nf₀ M) ρ = nf₀ (nf₀rep M ρ)
nfrep (φ imp ψ) ρ = nfrep φ ρ imp nfrep ψ ρ

nf₀rep-id : ∀ {V} {M : Meaning₀ V} → nf₀rep M (idRep V) ≡ M
nf₀rep-id {M = neutral N} = cong neutral nrep-id
nf₀rep-id {M = bot} = refl

nfrep-id : ∀ {V} {S} {M : Meaning V S} → nfrep M (idRep V) ≡ M
nfrep-id {M = nf₀ M} = cong nf₀ nf₀rep-id
nfrep-id {M = φ imp ψ} = cong₂ _imp_ nfrep-id nfrep-id

nf₀-comp : ∀ {U V W} {M : Meaning₀ U} {σ : Rep V W} {ρ : Rep U V} → nf₀rep M (σ •R ρ) ≡ nf₀rep (nf₀rep M ρ) σ
nf₀-comp {M = neutral N} = cong neutral nrep-comp
nf₀-comp {M = bot} = refl

nfrep-comp : ∀ {U V W S} {M : Meaning U S} {σ : Rep V W} {ρ : Rep U V} → nfrep M (σ •R ρ) ≡ nfrep (nfrep M ρ) σ
nfrep-comp {M = nf₀ M} = cong nf₀ nf₀-comp
nfrep-comp {M = φ imp ψ} = cong₂ _imp_ nfrep-comp nfrep-comp

decode-Meaning₀ : ∀ {V} → Meaning₀ V → Term V
decode-Meaning₀ (neutral N) = decode-Neutral N
decode-Meaning₀ bot = ⊥

decode-Meaning : ∀ {V} {S} → Meaning V S → Term V
decode-Meaning (nf₀ M) = decode-Meaning₀ M
decode-Meaning (φ imp ψ) = decode-Meaning φ ⊃ decode-Meaning ψ

decode-Meaning₀-rep : ∀ {U V} {M : Meaning₀ U} {ρ : Rep U V} → decode-Meaning₀ (nf₀rep M ρ) ≡ decode-Meaning₀ M 〈 ρ 〉
decode-Meaning₀-rep {M = neutral _} = decode-Neutral-rep
decode-Meaning₀-rep {M = bot} = refl

decode-Meaning-rep : ∀ {U V S} (M : Meaning U S) {ρ : Rep U V} → decode-Meaning (nfrep M ρ) ≡ decode-Meaning M 〈 ρ 〉
decode-Meaning-rep (nf₀ M) = decode-Meaning₀-rep {M = M}
decode-Meaning-rep (φ imp ψ) = cong₂ _⊃_ (decode-Meaning-rep φ) (decode-Meaning-rep ψ)

data ListMeaning (V : Alphabet) : List MeaningShape → Set where
  [] : ListMeaning V []
  _∷_ : ∀ {S SS} → Meaning V S → ListMeaning V SS → ListMeaning V (S ∷ SS)

listnfrep : ∀ {U V SS} → ListMeaning U SS → Rep U V → ListMeaning V SS
listnfrep [] _ = []
listnfrep (M ∷ MM) ρ = nfrep M ρ ∷ listnfrep MM ρ

listnfrep-comp : ∀ {U V W SS} {φ : ListMeaning U SS} {σ : Rep V W} {ρ : Rep U V} → listnfrep φ (σ •R ρ) ≡ listnfrep (listnfrep φ ρ) σ
listnfrep-comp {φ = []} = refl
listnfrep-comp {φ = x ∷ φ} = cong₂ _∷_ nfrep-comp listnfrep-comp

domMeaning : ∀ {V} {S} → Meaning V S → ListMeaning V (domS S)
domMeaning (nf₀ _) = []
domMeaning (φ imp ψ) = φ ∷ domMeaning ψ

domMeaning-rep : ∀ {U V S} {φ : Meaning U S} {ρ : Rep U V} → domMeaning (nfrep φ ρ) ≡ listnfrep (domMeaning φ) ρ
domMeaning-rep {φ = nf₀ x} = refl
domMeaning-rep {φ = φ imp ψ} {ρ} = cong (λ x → nfrep φ ρ ∷ x) domMeaning-rep

codMeaning : ∀ {V} {S} → Meaning V S → Meaning₀ V 
codMeaning (nf₀ M) = M
codMeaning (_ imp ψ) = codMeaning ψ

decode-Neutral-inj : ∀ {V} {φ ψ : Neutral V} → decode-Neutral φ ≡ decode-Neutral ψ → φ ≡ ψ
decode-Meaning₀-inj : ∀ {V} {φ ψ : Meaning₀ V} → decode-Meaning₀ φ ≡ decode-Meaning₀ ψ → φ ≡ ψ
decode-Meaning-inj : ∀ {V S} {φ ψ : Meaning V S} → decode-Meaning φ ≡ decode-Meaning ψ → φ ≡ ψ

decode-Neutral-inj {φ = var _} {var _} x≡y = cong var (var-inj x≡y)
decode-Neutral-inj {φ = var _} {app _ _} ()
decode-Neutral-inj {φ = app _ _} {var _} ()
decode-Neutral-inj {φ = app M N} {app M' N'} φ≡ψ = cong₂ app (decode-Neutral-inj (appT-injl φ≡ψ)) (appT-injr φ≡ψ)

decode-Meaning₀-inj {φ = neutral _} {ψ = neutral _} φ≡ψ = cong neutral (decode-Neutral-inj φ≡ψ)
decode-Meaning₀-inj {φ = neutral (var _)} {ψ = bot} ()
decode-Meaning₀-inj {φ = neutral (app _ _)} {ψ = bot} ()
decode-Meaning₀-inj {φ = bot} {ψ = neutral (var _)} ()
decode-Meaning₀-inj {φ = bot} {ψ = neutral (app _ _)} ()
decode-Meaning₀-inj {φ = bot} {bot} _ = refl

decode-Meaning-inj {S = nf₀} {nf₀ φ} {nf₀ ψ} φ≡ψ = cong nf₀ (decode-Meaning₀-inj φ≡ψ)
decode-Meaning-inj {S = S imp T} {φ imp φ'} {ψ imp ψ'} φ≡ψ = cong₂ _imp_ (decode-Meaning-inj (⊃-injl φ≡ψ)) (decode-Meaning-inj (⊃-injr φ≡ψ))
\end{code}
}

A term is \emph{m-normalizable} iff it reduces to a meaningful term.

\begin{code}
record MeanTerm {V} (φ : Term V) : Set where
  constructor MeanTermI
  field
    shape : MeaningShape
    meaning  : Meaning V shape
    red   : φ ↠ decode-Meaning meaning

MeanCtxt : ∀ {V} → Context V → Set
MeanCtxt {V} Γ = ∀ (p : Var V -Proof) → MeanTerm (typeof p Γ)
\end{code}
