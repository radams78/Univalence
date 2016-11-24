\AgdaHide{
\begin{code}
module PHOPL.Computable.Meaning where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Product hiding (map) renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red hiding (nf-is-nf)
open import PHOPL.Rules
open import PHOPL.Meta
\end{code}
}

A term is \emph{neutral} iff it has the form $x M_1 \cdots M_n$.
\begin{code}
SUBEXP : ∀ {C} → Kind C → SetFunctor
SUBEXP {C} K = record { 
  Fib = λ V → Subexp V C K ; 
  _〈〈_〉〉 = _〈_〉 ; 
  〈〈〉〉-id = rep-idRep ; 
  〈〈〉〉-comp = λ {_} {_} {_} {_} {_} {a} → rep-comp a }

snocList-rep : ∀ (F : SetFunctor) {U V} → snocList (SetFunctor.Fib F U) → Rep U V → snocList (SetFunctor.Fib F V)
snocList-rep _ [] _ = []
snocList-rep F (aa snoc a) ρ = snocList-rep F aa ρ snoc SetFunctor._〈〈_〉〉 F a ρ

snocList-rep-id : ∀ {F : SetFunctor} {V} {l : snocList (SetFunctor.Fib F V)} →
  snocList-rep F l (idRep V) ≡ l
snocList-rep-id {l = []} = refl
snocList-rep-id {F} {l = aa snoc a} = cong₂ _snoc_ (snocList-rep-id {F}) (SetFunctor.〈〈〉〉-id F)

snocList-rep-comp : ∀ {F : SetFunctor} {U V W} {l : snocList (SetFunctor.Fib F U)}
  {σ : Rep V W} {ρ : Rep U V} → snocList-rep F l (σ •R ρ) ≡ snocList-rep F (snocList-rep F l ρ) σ
snocList-rep-comp {l = []} = refl
snocList-rep-comp {F} {l = aa snoc a} = cong₂ _snoc_ (snocList-rep-comp {F}) (SetFunctor.〈〈〉〉-comp F)

SNOCLISTF : SetFunctor → SetFunctor
SNOCLISTF F = record { 
  Fib = λ V → snocList (SetFunctor.Fib F V) ; 
  _〈〈_〉〉 = snocList-rep F ; 
  〈〈〉〉-id = snocList-rep-id ; 
  〈〈〉〉-comp = snocList-rep-comp }

prod-rep : ∀ {F G : SetFunctor} {U V : Alphabet} → 
  SetFunctor.Fib F U × SetFunctor.Fib G U → Rep U V → SetFunctor.Fib F V × SetFunctor.Fib G V
prod-rep {F} {G} {U} {V} (a ,p b) ρ = (SetFunctor._〈〈_〉〉 F a ρ ,p SetFunctor._〈〈_〉〉 G b ρ)

prod-rep-id : ∀ {F G : SetFunctor} {V : Alphabet} {p : SetFunctor.Fib F V × SetFunctor.Fib G V} → prod-rep {F} {G} {V} p (idRep V) ≡ p
prod-rep-id {F} {G} {p = (_ ,p _)} = cong₂ _,p_ (SetFunctor.〈〈〉〉-id F) (SetFunctor.〈〈〉〉-id G)

prod-rep-comp : ∀ {F G : SetFunctor} {U V W : Alphabet} {σ : Rep V W} {ρ : Rep U V} →
  {p : SetFunctor.Fib F U × SetFunctor.Fib G U} →
  prod-rep {F} {G} {U} p (σ •R ρ) ≡ prod-rep {F} {G} (prod-rep {F} {G} p ρ) σ
prod-rep-comp {F} {G} {p = (_ ,p _)} = cong₂ _,p_ (SetFunctor.〈〈〉〉-comp F) (SetFunctor.〈〈〉〉-comp G)

PROD : SetFunctor → SetFunctor → SetFunctor
PROD F G = record { 
  Fib = λ V → SetFunctor.Fib F V × SetFunctor.Fib G V ; 
  _〈〈_〉〉 = prod-rep {F} {G};
  〈〈〉〉-id = prod-rep-id {F} {G} ; 
  〈〈〉〉-comp = prod-rep-comp {F} {G} }

data Neutral (V : Alphabet) : Set where
  app : Var V -Term → snocList (Term V) → Neutral V

nrep : ∀ {U V} → Neutral U → Rep U V → Neutral V
nrep (app x MM) ρ = app (ρ _ x) (snocmap (λ M → M 〈 ρ 〉) MM)

nrep-id : ∀ {V} {N : Neutral V} → nrep N (idRep V) ≡ N
nrep-id {N = app x MM} = cong (app x) (≡-Reasoning.trans (snocmapcong (λ _ → rep-idRep)) snocmap-id)

nrep-comp : ∀ {U V W} {N : Neutral U} {ρ' : Rep V W} {ρ : Rep U V} → nrep N (ρ' •R ρ) ≡ nrep (nrep N ρ) ρ'
nrep-comp {N = app x MM} {ρ'} {ρ} = cong (app (ρ' _ (ρ _ x))) (let open ≡-Reasoning in begin 
   snocmap (λ M → M 〈 ρ' •R ρ 〉) MM
  ≡⟨ snocmapcong (λ M → rep-comp M) ⟩
    snocmap (λ M → M 〈 ρ 〉 〈 ρ' 〉) MM
  ≡⟨ snocmap-comp ⟩
    snocmap (λ M → M 〈 ρ' 〉) (snocmap (λ M → M 〈 ρ 〉) MM)
  ∎)

decode-Neutral : ∀ {V} → Neutral V → Term V
decode-Neutral (app x MM) = APPl (var x) MM

decode-Neutral-rep : ∀ {U V} {N : Neutral U} {ρ : Rep U V} → decode-Neutral (nrep N ρ) ≡ decode-Neutral N 〈 ρ 〉
decode-Neutral-rep {N = app x MM} {ρ} = Prelims.sym (APPl-rep {NN = MM})
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
decode-Meaning₀-rep {M = neutral M} = decode-Neutral-rep {N = M}
decode-Meaning₀-rep {M = bot} = refl

decode-Meaning-rep : ∀ {U V S} (M : Meaning U S) {ρ : Rep U V} → decode-Meaning (nfrep M ρ) ≡ decode-Meaning M 〈 ρ 〉
decode-Meaning-rep (nf₀ M) = decode-Meaning₀-rep {M = M}
decode-Meaning-rep (φ imp ψ) = cong₂ _⊃_ (decode-Meaning-rep φ) (decode-Meaning-rep ψ)

ListMeaning' : Alphabet → List MeaningShape → Set
ListMeaning' V = HetL LIST (Meaning V)

ListMeaning : ∀ (V : Alphabet) → List MeaningShape → Set
ListMeaning V = HetList (Meaning V)

listnfrep' : ∀ {U V SS} → ListMeaning' U SS → Rep U V → ListMeaning' V SS
listnfrep' {U} {V} {SS} MM ρ = HetL-map {F = LIST} {aa = SS} (λ _ M → nfrep M ρ) MM

listnfrep : ∀ {U V SS} → ListMeaning U SS → Rep U V → ListMeaning V SS
listnfrep [] _ = []
listnfrep (M ∷ MM) ρ = nfrep M ρ ∷ listnfrep MM ρ

HetL-map-comp : ∀ {A : Set} {F : FoldFunc} {B C D : A → Set} {aa : FoldFunc.F F A} 
  {g : ∀ a → C a → D a} {f : ∀ a → B a → C a} {bb : HetL F B aa} →
  HetL-map {F = F} (λ a b → g a (f a b)) bb ≡ HetL-map {F = F} g (HetL-map {F = F} f bb)
HetL-map-comp {A} {F} {B} {C} {D} {aa} {g} {f} {bb} = {!!}

listnfrep-comp' : ∀ {U V W SS} {φ : ListMeaning' U SS} {σ : Rep V W} {ρ : Rep U V} → listnfrep' {SS = SS} φ (σ •R ρ) ≡ listnfrep' {SS = SS} (listnfrep' {SS = SS} φ ρ) σ
listnfrep-comp' {U} {V} {W} {SS} {φ} {σ} {ρ} = {!!}

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

APPvar-injl : ∀ {V} {x y : Var V -Term} {MM NN : snocList (Term V)} →
  APPl (var x) MM ≡ APPl (var y) NN → x ≡ y
APPvar-injl {MM = []} {[]} x≡y = var-inj x≡y
APPvar-injl {MM = []} {_ snoc _} ()
APPvar-injl {MM = _ snoc _} {[]} ()
APPvar-injl {MM = MM snoc M} {NN snoc N} xMM≡yNN = APPvar-injl {MM = MM} {NN} (appT-injl xMM≡yNN)

APPvar-injr : ∀ {V} {x y : Var V -Term} {MM NN : snocList (Term V)} →
  APPl (var x) MM ≡ APPl (var y) NN → MM ≡ NN
APPvar-injr {MM = []} {[]} _ = refl
APPvar-injr {MM = []} {_ snoc _} ()
APPvar-injr {MM = _ snoc _} {[]} ()
APPvar-injr {MM = MM snoc M} {NN snoc N} xMM≡yNN = cong₂ _snoc_ (APPvar-injr {MM = MM} {NN} (appT-injl xMM≡yNN)) (appT-injr xMM≡yNN)

decode-Neutral-inj {φ = app x MM} {app y NN} xMM≡yNN = cong₂ app (APPvar-injl {MM = MM} {NN} xMM≡yNN) (APPvar-injr xMM≡yNN)

decode-Meaning₀-inj {φ = neutral _} {ψ = neutral _} φ≡ψ = cong neutral (decode-Neutral-inj φ≡ψ)
decode-Meaning₀-inj {φ = neutral (app _ [])} {bot} ()
decode-Meaning₀-inj {φ = neutral (app _ (_ snoc _))} {bot} ()
decode-Meaning₀-inj {φ = bot} {neutral (app x [])} ()
decode-Meaning₀-inj {φ = bot} {neutral (app x (MM snoc x₁))} ()
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

\begin{lemma}
Every strongly normalizable term is m-normalizable.
\end{lemma}

%TODO Agda

\begin{code}
postulate not-nf₀-conv-imp : ∀ {V} {M : Meaning₀ V} {φ ψ : Term V} → decode-Meaning₀ M ≃ φ ⊃ ψ → Empty

decode-not-app : ∀ {V} → not-app V  → Term V
decode-not-app (navar x) = var x
decode-not-app na⊥ = ⊥
decode-not-app (na⊃ φ ψ) = φ ⊃ ψ
decode-not-app (naΛ A M) = ΛT A M

head : ∀ {V} → Term V → not-app V
head (var x) = navar x
head (app -bot _) = na⊥
head (app -imp (φ ∷ ψ ∷ [])) = na⊃ φ ψ
head (app (-lamTerm A) (M ∷ [])) = naΛ A M
head (app -appTerm (M ∷ _ ∷ [])) = head M

tail : ∀ {V} → Term V → snocList (Term V)
tail (var _) = []
tail (app -appTerm (M ∷ N ∷ [])) = tail M snoc N
tail (app _ _) = []

head-tail : ∀ {V} {M : Term V} → M ≡ APPl (decode-not-app (head M)) (tail M)
head-tail {M = var x} = refl
head-tail {M = app -bot []} = refl
head-tail {M = app -imp (φ ∷ ψ ∷ [])} = refl
head-tail {M = app (-lamTerm A) (M ∷ [])} = refl
head-tail {M = app -appTerm (M ∷ N ∷ [])} = cong (λ x → appT x N) (head-tail {M = M})

not-⊃MMM-typed : ∀ {V} {Γ : Context V} {φ ψ} MM {N A} → Γ ⊢ appT (APPl (φ ⊃ ψ) MM) N ∶ A → Empty
not-⊃MMM-typed [] (appR () _)
not-⊃MMM-typed (MM snoc M) (appR Γ⊢MMM∶A⇛B Γ⊢N∶A) = not-⊃MMM-typed MM Γ⊢MMM∶A⇛B
\end{code}
