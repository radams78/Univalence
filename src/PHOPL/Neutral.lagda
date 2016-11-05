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

\begin{code}
\end{code}

\AgdaHide{
\begin{code}

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
