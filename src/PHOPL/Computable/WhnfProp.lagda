\AgdaHide{
\begin{code}
module PHOPL.Computable.WhnfProp where
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

Note first that (using Generation) a normal form of type $\Omega$ is either $\bot$, or a neutral term, or $\phi \supset \psi$ where $\phi$ and $\psi$ are normal forms of type $\Omega$.

\AgdaHide{
\begin{code}
--TODO Two characterisations of normal forms???
data Neutral (V : Alphabet) : Set where
  var : Var V -Term → Neutral V
  app : Neutral V → Term V → Neutral V

data Whnf₀ (V : Alphabet) : Set where
  neutral : Neutral V → Whnf₀ V
  bot : Whnf₀ V

data WhnfShape : Set where
  nf₀ : WhnfShape
  _imp_ : WhnfShape → WhnfShape → WhnfShape

data Whnf (V : Alphabet) : WhnfShape → Set where
  nf₀ : Whnf₀ V → Whnf V nf₀
  _imp_ : ∀ {S} {T} → Whnf V S → Whnf V T → Whnf V (S imp T)

nrep : ∀ {U V} → Neutral U → Rep U V → Neutral V
nf₀rep : ∀ {U V} → Whnf₀ U → Rep U V → Whnf₀ V
nfrep : ∀ {U} {V} {S} → Whnf U S → Rep U V → Whnf V S

nrep (var x) ρ = var (ρ -Term x)
nrep (app M N) ρ = app (nrep M ρ) (N 〈 ρ 〉)

nf₀rep (neutral N) ρ = neutral (nrep N ρ)
nf₀rep bot _ = bot

nfrep (nf₀ M) ρ = nf₀ (nf₀rep M ρ)
nfrep (φ imp ψ) ρ = nfrep φ ρ imp nfrep ψ ρ

nrep-id : ∀ {V} {N : Neutral V} → nrep N (idRep V) ≡ N
nf₀rep-id : ∀ {V} {M : Whnf₀ V} → nf₀rep M (idRep V) ≡ M
nfrep-id : ∀ {V} {S} {M : Whnf V S} → nfrep M (idRep V) ≡ M

nrep-id {N = var _} = refl
nrep-id {N = app N M} = cong₂ app nrep-id rep-idRep

nf₀rep-id {M = neutral N} = cong neutral nrep-id
nf₀rep-id {M = bot} = refl

nfrep-id {M = nf₀ M} = cong nf₀ nf₀rep-id
nfrep-id {M = φ imp ψ} = cong₂ _imp_ nfrep-id nfrep-id

nrep-comp : ∀ {U V W} {N : Neutral U} {ρ' : Rep V W} {ρ : Rep U V} → nrep N (ρ' •R ρ) ≡ nrep (nrep N ρ) ρ'
nf₀-comp : ∀ {U V W} {M : Whnf₀ U} {σ : Rep V W} {ρ : Rep U V} → nf₀rep M (σ •R ρ) ≡ nf₀rep (nf₀rep M ρ) σ
nfrep-comp : ∀ {U V W S} {M : Whnf U S} {σ : Rep V W} {ρ : Rep U V} → nfrep M (σ •R ρ) ≡ nfrep (nfrep M ρ) σ

nrep-comp {N = var x} = refl
nrep-comp {N = app N N'} = cong₂ app nrep-comp (rep-comp N')

nf₀-comp {M = neutral N} = cong neutral nrep-comp
nf₀-comp {M = bot} = refl

nfrep-comp {M = nf₀ M} = cong nf₀ nf₀-comp
nfrep-comp {M = φ imp ψ} = cong₂ _imp_ nfrep-comp nfrep-comp

decode-Neutral : ∀ {V} → Neutral V → Term V
decode-Whnf₀ : ∀ {V} → Whnf₀ V → Term V
decode-Whnf : ∀ {V} {S} → Whnf V S → Term V

decode-Neutral (var x) = var x
decode-Neutral (app M N) = appT (decode-Neutral M) N

decode-Whnf₀ (neutral N) = decode-Neutral N
decode-Whnf₀ bot = ⊥

decode-Whnf (nf₀ M) = decode-Whnf₀ M
decode-Whnf (φ imp ψ) = decode-Whnf φ ⊃ decode-Whnf ψ

decode-Neutral-rep : ∀ {U V} {N : Neutral U} {ρ : Rep U V} → decode-Neutral (nrep N ρ) ≡ decode-Neutral N 〈 ρ 〉
decode-Whnf₀-rep : ∀ {U V} {M : Whnf₀ U} {ρ : Rep U V} → decode-Whnf₀ (nf₀rep M ρ) ≡ decode-Whnf₀ M 〈 ρ 〉
decode-Whnf-rep : ∀ {U V S} (M : Whnf U S) {ρ : Rep U V} → decode-Whnf (nfrep M ρ) ≡ decode-Whnf M 〈 ρ 〉

decode-Neutral-rep {N = var _} = refl
decode-Neutral-rep {N = app _ M} {ρ} = cong₂ appT decode-Neutral-rep refl

decode-Whnf₀-rep {M = neutral _} = decode-Neutral-rep
decode-Whnf₀-rep {M = bot} = refl

decode-Whnf-rep (nf₀ M) = decode-Whnf₀-rep {M = M}
decode-Whnf-rep (φ imp ψ) = cong₂ _⊃_ (decode-Whnf-rep φ) (decode-Whnf-rep ψ)

domS : WhnfShape → List WhnfShape
domS nf₀ = []
domS (S imp T) = S ∷ domS T

data ListWhnf (V : Alphabet) : List WhnfShape → Set where
  [] : ListWhnf V []
  _∷_ : ∀ {S SS} → Whnf V S → ListWhnf V SS → ListWhnf V (S ∷ SS)

listnfrep : ∀ {U V SS} → ListWhnf U SS → Rep U V → ListWhnf V SS
listnfrep [] _ = []
listnfrep (M ∷ MM) ρ = nfrep M ρ ∷ listnfrep MM ρ

listnfrep-comp : ∀ {U V W SS} {φ : ListWhnf U SS} {σ : Rep V W} {ρ : Rep U V} → listnfrep φ (σ •R ρ) ≡ listnfrep (listnfrep φ ρ) σ
listnfrep-comp {φ = []} = refl
listnfrep-comp {φ = x ∷ φ} = cong₂ _∷_ nfrep-comp listnfrep-comp

domWhnf : ∀ {V} {S} → Whnf V S → ListWhnf V (domS S)
domWhnf (nf₀ _) = []
domWhnf (φ imp ψ) = φ ∷ domWhnf ψ

domWhnf-rep : ∀ {U V S} {φ : Whnf U S} {ρ : Rep U V} → domWhnf (nfrep φ ρ) ≡ listnfrep (domWhnf φ) ρ
domWhnf-rep {φ = nf₀ x} = refl
domWhnf-rep {φ = φ imp ψ} {ρ} = cong (λ x → nfrep φ ρ ∷ x) domWhnf-rep

codWhnf : ∀ {V} {S} → Whnf V S → Whnf₀ V 
codWhnf (nf₀ M) = M
codWhnf (_ imp ψ) = codWhnf ψ

decode-Neutral-inj : ∀ {V} {φ ψ : Neutral V} → decode-Neutral φ ≡ decode-Neutral ψ → φ ≡ ψ
decode-Whnf₀-inj : ∀ {V} {φ ψ : Whnf₀ V} → decode-Whnf₀ φ ≡ decode-Whnf₀ ψ → φ ≡ ψ
decode-Whnf-inj : ∀ {V S} {φ ψ : Whnf V S} → decode-Whnf φ ≡ decode-Whnf ψ → φ ≡ ψ

decode-Neutral-inj {φ = var _} {var _} x≡y = cong var (var-inj x≡y)
decode-Neutral-inj {φ = var _} {app _ _} ()
decode-Neutral-inj {φ = app _ _} {var _} ()
decode-Neutral-inj {φ = app M N} {app M' N'} φ≡ψ = cong₂ app (decode-Neutral-inj (appT-injl φ≡ψ)) (appT-injr φ≡ψ)

decode-Whnf₀-inj {φ = neutral _} {ψ = neutral _} φ≡ψ = cong neutral (decode-Neutral-inj φ≡ψ)
decode-Whnf₀-inj {φ = neutral (var _)} {ψ = bot} ()
decode-Whnf₀-inj {φ = neutral (app _ _)} {ψ = bot} ()
decode-Whnf₀-inj {φ = bot} {ψ = neutral (var _)} ()
decode-Whnf₀-inj {φ = bot} {ψ = neutral (app _ _)} ()
decode-Whnf₀-inj {φ = bot} {bot} _ = refl

decode-Whnf-inj {S = nf₀} {nf₀ φ} {nf₀ ψ} φ≡ψ = cong nf₀ (decode-Whnf₀-inj φ≡ψ)
decode-Whnf-inj {S = S imp T} {φ imp φ'} {ψ imp ψ'} φ≡ψ = cong₂ _imp_ (decode-Whnf-inj (⊃-injl φ≡ψ)) (decode-Whnf-inj (⊃-injr φ≡ψ))
\end{code}
}
