\AgdaHide{
\begin{code}
module PHOPL.Neutral where

open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Data.List
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red
open import PHOPL.PathSub
\end{code}
}

A term is \emph{neutral} iff it has the form $x M_1 \cdots M_n$.

\begin{code}
data Neutral (V : Alphabet) : Set where
  var : Var V -Term → Neutral V
  app : Neutral V → Term V → Neutral V
\end{code}

\AgdaHide{
\begin{code}
decode-Neutral : ∀ {V} → Neutral V → Term V
decode-Neutral (var x) = var x
decode-Neutral (app M N) = appT (decode-Neutral M) N

nrep : ∀ {U} {V} → Neutral U → Rep U V → Neutral V
nrep (var x) ρ = var (ρ -Term x)
nrep (app M N) ρ = app (nrep M ρ) (N 〈 ρ 〉)

nrep-comp : ∀ {U V W} {ρ' : Rep V W} {ρ : Rep U V} {N} → nrep N (ρ' •R ρ) ≡ nrep (nrep N ρ) ρ'
nrep-comp {N = var x} = refl
nrep-comp {N = app N N'} = cong₂ app nrep-comp (rep-comp N')

private neutral-red' : ∀ {V} {N : Neutral V} {M₁} {M₂} → M₁ ↠ M₂ → decode-Neutral N ≡ M₁ →
                     Σ[ N' ∈ Neutral V ] decode-Neutral N' ≡ M₂
neutral-red' {N = var _} (inc (redex (R₀R ()))) _
neutral-red' {N = var _} (inc (redex (βR βT))) ()
neutral-red' {N = app (var _) _} (inc (redex (R₀R ()))) _
neutral-red' {N = app (var _) _} (inc (redex (βR βT))) xF≡ΛMN = ⊥-elim (var-not-Λ (appT-injl xF≡ΛMN))
neutral-red' {N = app (app _ _) _} (inc (redex (R₀R ()))) _
neutral-red' {N = app (app _ _) _} (inc (redex (βR βT))) EF≡ΛMN = ⊥-elim (app-not-Λ (appT-injl EF≡ΛMN))
neutral-red' {N = var _} (inc (app _)) ()
neutral-red' {N = app _ _} (inc (app {c = -bot} _)) ()
neutral-red' {N = app _ _} (inc (app {c = -imp} _)) ()
neutral-red' {N = app N P} (inc (app {c = -appTerm} (appl {F = F ∷ []} E⇒E'))) NP≡EF = 
  let (N' ,p N'≡E') = neutral-red' (inc E⇒E') (appT-injl NP≡EF) in
  app N' P ,p cong₂ appT N'≡E' (appT-injr NP≡EF)
neutral-red' {N = app N P} (inc (app {c = -appTerm} (appr (appl {E' = F'} {F = []} F↠F')))) NP≡EF = app N F' ,p cong (λ x → appT x F') (appT-injl NP≡EF)
neutral-red' {N = app _ _} (inc (app {c = -appTerm} (appr (appr ())))) _
neutral-red' {N = app _ _} (inc (app {c = -lamTerm x} _)) ()
neutral-red' {N = N} ref N≡M₁ = N ,p N≡M₁
neutral-red' (trans M₁↠M₂ M₂↠M₃) N≡M₁ = 
  let (_ ,p N₂≡M₂) = neutral-red' M₁↠M₂ N≡M₁ in
  neutral-red' M₂↠M₃ N₂≡M₂
\end{code}
}

\begin{lemma}
If $M \twoheadrightarrow N$ and $M$ is neutral, then $N$ is neutral.
\end{lemma}

\begin{code}
neutral-red : ∀ {V} {N : Neutral V} {M} → decode-Neutral N ↠ M →
  Σ[ N' ∈ Neutral V ] decode-Neutral N' ≡ M
\end{code}

\AgdaHide{
\begin{code}
neutral-red N↠M = neutral-red' N↠M refl
\end{code}
}
