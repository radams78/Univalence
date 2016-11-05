\AgdaHide{
\begin{code}
module PHOPL.Computable.NFProp where
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
data NeutralShape : Set
data Nf₀Shape : Set
data NfShape : Set

data NeutralShape where
  var : NeutralShape
  app : NeutralShape → NfShape → NeutralShape

data Nf₀Shape where
  neutral : NeutralShape → Nf₀Shape
  bot : Nf₀Shape

data NfShape where
  nf₀ : Nf₀Shape → NfShape
  _imp_ : NfShape → NfShape → NfShape

data Neutral (V : Alphabet) : NeutralShape → Set
data Nf₀ (V : Alphabet) : Nf₀Shape → Set
data Nf (V : Alphabet) : NfShape → Set

data Neutral V where
  var : Var V -Term → Neutral V var
  app : ∀ {S T} → Neutral V S → Nf V T → Neutral V (app S T)

data Nf₀ V where
  neutral : ∀ {S} → Neutral V S → Nf₀ V (neutral S)
  bot : Nf₀ V bot

data Nf V where
  nf₀ : ∀ {S} → Nf₀ V S → Nf V (nf₀ S)
  _imp_ : ∀ {S} {T} → Nf V S → Nf V T → Nf V (S imp T)

nrep : ∀ {U V S} → Neutral U S → Rep U V → Neutral V S
nf₀rep : ∀ {U V S} → Nf₀ U S → Rep U V → Nf₀ V S
nfrep : ∀ {U} {V} {S} → Nf U S → Rep U V → Nf V S

nrep (var x) ρ = var (ρ -Term x)
nrep (app M N) ρ = app (nrep M ρ) (nfrep N ρ)

nf₀rep (neutral N) ρ = neutral (nrep N ρ)
nf₀rep bot _ = bot

nfrep (nf₀ M) ρ = nf₀ (nf₀rep M ρ)
nfrep (φ imp ψ) ρ = nfrep φ ρ imp nfrep ψ ρ

nrep-id : ∀ {V S} {N : Neutral V S} → nrep N (idRep V) ≡ N
nf₀rep-id : ∀ {V S} {M : Nf₀ V S} → nf₀rep M (idRep V) ≡ M
nfrep-id : ∀ {V} {S} {M : Nf V S} → nfrep M (idRep V) ≡ M

nrep-id {N = var _} = refl
nrep-id {N = app N M} = cong₂ app nrep-id nfrep-id

nf₀rep-id {M = neutral N} = cong neutral nrep-id
nf₀rep-id {M = bot} = refl

nfrep-id {M = nf₀ M} = cong nf₀ nf₀rep-id
nfrep-id {M = φ imp ψ} = cong₂ _imp_ nfrep-id nfrep-id

nrep-comp : ∀ {U V W S} {N : Neutral U S} {ρ' : Rep V W} {ρ : Rep U V} → nrep N (ρ' •R ρ) ≡ nrep (nrep N ρ) ρ'
nf₀-comp : ∀ {U V W S} {M : Nf₀ U S} {σ : Rep V W} {ρ : Rep U V} → nf₀rep M (σ •R ρ) ≡ nf₀rep (nf₀rep M ρ) σ
nf-comp : ∀ {U V W S} {M : Nf U S} {σ : Rep V W} {ρ : Rep U V} → nfrep M (σ •R ρ) ≡ nfrep (nfrep M ρ) σ

nrep-comp {N = var x} = refl
nrep-comp {N = app N N'} = cong₂ app nrep-comp nf-comp

nf₀-comp {M = neutral N} = cong neutral nrep-comp
nf₀-comp {M = bot} = refl

nf-comp {M = nf₀ M} = cong nf₀ nf₀-comp
nf-comp {M = φ imp ψ} = cong₂ _imp_ nf-comp nf-comp

decode-Neutral : ∀ {V S} → Neutral V S → Term V
decode-Nf₀ : ∀ {V S} → Nf₀ V S → Term V
decode-Nf : ∀ {V} {S} → Nf V S → Term V

decode-Neutral (var x) = var x
decode-Neutral (app M N) = appT (decode-Neutral M) (decode-Nf N)

decode-Nf₀ (neutral N) = decode-Neutral N
decode-Nf₀ bot = ⊥

decode-Nf (nf₀ M) = decode-Nf₀ M
decode-Nf (φ imp ψ) = decode-Nf φ ⊃ decode-Nf ψ

decode-Neutral-rep : ∀ {U V S} {N : Neutral U S} {ρ : Rep U V} → decode-Neutral (nrep N ρ) ≡ decode-Neutral N 〈 ρ 〉
decode-Nf₀-rep : ∀ {U V S} {M : Nf₀ U S} {ρ : Rep U V} → decode-Nf₀ (nf₀rep M ρ) ≡ decode-Nf₀ M 〈 ρ 〉
decode-Nf-rep : ∀ {U V S} (M : Nf U S) {ρ : Rep U V} → decode-Nf (nfrep M ρ) ≡ decode-Nf M 〈 ρ 〉

decode-Neutral-rep {N = var _} = refl
decode-Neutral-rep {N = app _ M} {ρ} = cong₂ appT decode-Neutral-rep (decode-Nf-rep M)

decode-Nf₀-rep {M = neutral _} = decode-Neutral-rep
decode-Nf₀-rep {M = bot} = refl

decode-Nf-rep (nf₀ M) = decode-Nf₀-rep {M = M}
decode-Nf-rep (φ imp ψ) = cong₂ _⊃_ (decode-Nf-rep φ) (decode-Nf-rep ψ)

neutral-is-nf : ∀ {V S} {N : Neutral V S} {E} → decode-Neutral N ⇒ E → Empty
nf₀-is-nf : ∀ {V S} {M : Nf₀ V S} {E} → decode-Nf₀ M ⇒ E → Empty
nf-is-nf : ∀ {V S} {M : Nf V S} {E} → decode-Nf M ⇒ E → Empty

neutral-is-nf {N = var _} ()
neutral-is-nf {N = app (var _) _} (redex (βR ()))
neutral-is-nf {N = app (var _) _} (redex (R₀R ()))
neutral-is-nf {N = app (app _ _) _} (redex (βR ()))
neutral-is-nf {N = app (app _ _) _} (redex (R₀R ()))
neutral-is-nf {N = app N M} (app (appl N⇒E)) = (neutral-is-nf N⇒E)
neutral-is-nf {N = app N M} (app (appr (appl N⇒E))) = (nf-is-nf {M = M} N⇒E)
neutral-is-nf {N = app N M} (app (appr (appr ())))

nf₀-is-nf {M = neutral N} M⇒E = neutral-is-nf M⇒E
nf₀-is-nf {M = bot} (redex (βR ()))
nf₀-is-nf {M = bot} (redex (R₀R ()))
nf₀-is-nf {M = bot} (app ())

nf-is-nf {M = nf₀ M} M⇒E = nf₀-is-nf {M = M} M⇒E
nf-is-nf {M = _ imp _} (redex (βR ()))
nf-is-nf {M = _ imp _} (redex (R₀R ()))
nf-is-nf {M = φ imp _} (app (appl φ⇒E)) = nf-is-nf {M = φ} φ⇒E
nf-is-nf {M = _ imp ψ} (app (appr (appl ψ⇒E))) = nf-is-nf {M = ψ} ψ⇒E
nf-is-nf {M = _ imp _} (app (appr (appr ())))

domS : NfShape → List NfShape
domS (nf₀ _) = []
domS (S imp T) = S ∷ domS T

codS : NfShape → Nf₀Shape
codS (nf₀ S) = S
codS (_ imp T) = codS T

data ListNf (V : Alphabet) : List NfShape → Set where
  [] : ListNf V []
  _∷_ : ∀ {S SS} → Nf V S → ListNf V SS → ListNf V (S ∷ SS)

listnfrep : ∀ {U V SS} → ListNf U SS → Rep U V → ListNf V SS
listnfrep [] _ = []
listnfrep (M ∷ MM) ρ = nfrep M ρ ∷ listnfrep MM ρ

domNf : ∀ {V} {S} → Nf V S → ListNf V (domS S)
domNf (nf₀ _) = []
domNf (φ imp ψ) = φ ∷ domNf ψ

codNf : ∀ {V} {S} → Nf V S → Nf₀ V (codS S)
codNf (nf₀ M) = M
codNf (_ imp ψ) = codNf ψ
\end{code}
}
