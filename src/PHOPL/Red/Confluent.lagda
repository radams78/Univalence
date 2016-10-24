\AgdaHide{
\begin{code}
module PHOPL.Red.Confluent where
open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red

postulate Critical-Pairs : ∀ {V} {K} {C} {c : Con (SK C K)} {E : ListAbs V C} {F} {G} → R c E F → R c E G → Σ[ H ∈ Expression V K ] ((F ↠ H) × (G ↠ H))
{-Critical-Pairs βT βT = _ ,p ref ,p ref
Critical-Pairs βR βR = _ ,p ref ,p ref
Critical-Pairs plus-ref plus-ref = _ ,p ref ,p ref
Critical-Pairs minus-ref minus-ref = _ ,p ref ,p ref
Critical-Pairs plus-univ plus-univ = _ ,p ref ,p ref
Critical-Pairs minus-univ minus-univ = _ ,p ref ,p ref
Critical-Pairs ref⊃*univ ref⊃*univ = _ ,p ref ,p ref
Critical-Pairs univ⊃*ref univ⊃*ref = _ ,p ref ,p ref
Critical-Pairs univ⊃*univ univ⊃*univ = _ ,p ref ,p ref
Critical-Pairs ref⊃*ref ref⊃*ref = _ ,p ref ,p ref
Critical-Pairs refref refref = _ ,p ref ,p ref
Critical-Pairs βE βE = _ ,p ref ,p ref
Critical-Pairs reflamvar reflamvar = _ ,p ref ,p ref
Critical-Pairs reflam⊃* reflam⊃* = _ ,p ref ,p ref
Critical-Pairs reflamuniv reflamuniv = _ ,p ref ,p ref
Critical-Pairs reflamλλλ reflamλλλ = _ ,p ref ,p ref -}

postulate pre-confluent-case₁ : ∀ {V φ ψ χ δ ε P} → univ ψ χ δ ε ⇒ P →
                              Σ[ Q ∈ Path V ] R -imp* (reff φ ∷ P ∷ []) Q × ru-redex φ ψ χ δ ε ↠ Q
{-pre-confluent-case₁ {V} {φ} {ψ} {χ} {δ} {ε} {P} = univ-osrE 
    {C = λ P → Σ[ Q ∈ Path V ] R -imp* (reff φ ∷ P ∷ []) Q × ru-redex φ ψ χ δ ε ↠ Q}
    (λ ψ' ψ⇒ψ' → _ ,p ref⊃*univ ,p ru-redex-red δ δ ε ε ref (inc ψ⇒ψ') ref ref ref)
    (λ χ' χ⇒χ' → _ ,p ref⊃*univ ,p ru-redex-red δ δ ε ε ref ref (inc χ⇒χ') ref ref)
    (λ δ' δ⇒δ' → _ ,p ref⊃*univ ,p ru-redex-red δ δ' ε ε ref ref ref (inc δ⇒δ') ref)
    (λ ε' ε⇒ε' → _ ,p ref⊃*univ ,p ru-redex-red δ δ ε ε' ref ref ref ref (inc ε⇒ε')) -}

postulate pre-confluent-case₂ : ∀ {V φ φ' ψ χ δ ε} → φ ⇒ φ' → Σ[ Q ∈ Path V ] R -imp* (reff φ' ∷ univ ψ χ δ ε ∷ []) Q × ru-redex φ ψ χ δ ε ↠ Q
--pre-confluent-case₂ {V} {φ} {φ'} {ψ} {χ} {δ} {ε} φ⇒φ' = _ ,p ref⊃*univ ,p ru-redex-red δ δ ε ε (inc φ⇒φ') ref ref ref ref

postulate pre-confluent-case₃ : ∀ {V φ ψ χ δ ε P} → univ φ ψ δ ε ⇒ P → Σ[ Q ∈ Path V ] R -imp* (P ∷ reff χ ∷ []) Q × ur-redex φ ψ χ δ ε ↠ Q
{- pre-confluent-case₃ {V} {φ} {ψ} {χ} {δ} {ε} {P} = univ-osrE
  {C = λ P → Σ-syntax (Path V) (λ Q →
    R -imp* (P ∷ reff χ ∷ []) Q × ur-redex φ ψ χ δ ε ↠ Q)}
  (λ φ' φ⇒φ' → _ ,p univ⊃*ref ,p ur-redex-red δ δ ε ε (inc φ⇒φ') ref ref ref ref)
  (λ ψ' ψ⇒ψ' → _ ,p univ⊃*ref ,p ur-redex-red δ δ ε ε ref (inc ψ⇒ψ') ref ref ref)
  (λ δ' δ⇒δ' → _ ,p univ⊃*ref ,p ur-redex-red δ δ' ε ε ref ref ref (inc δ⇒δ') ref)
  (λ ε' ε⇒ε' → _ ,p univ⊃*ref ,p ur-redex-red δ δ ε ε' ref ref ref ref (inc ε⇒ε')) -}

postulate pre-confluent-case₄ : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ' ε ε' P} → univ φ ψ δ ε ⇒ P → 
                              Σ[ Q ∈ Path V ] R -imp* (P ∷ univ φ' ψ' δ' ε' ∷ []) Q × uu-redex φ φ' ψ ψ' δ δ' ε ε' ↠ Q
{- pre-confluent-case₄ {V} {φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'} {P} = univ-osrE
  {C = λ P → Σ[ Q ∈ Path V ] R -imp* (P ∷ univ φ' ψ' δ' ε' ∷ []) Q × uu-redex φ φ' ψ ψ' δ δ' ε ε' ↠ Q}
  (λ φ'' φ⇒φ'' → _ ,p univ⊃*univ ,p uu-redex-red δ δ' ε ε' (inc φ⇒φ'') ref ref ref ref ref ref ref)
  (λ ψ'' ψ⇒ψ'' → _ ,p univ⊃*univ ,p uu-redex-red δ δ' ε ε' ref ref (inc ψ⇒ψ'') ref ref ref ref ref)
  (λ δ'' δ⇒δ'' → _ ,p univ⊃*univ ,p uu-redex-red δ δ' ε ε' ref ref ref ref (inc δ⇒δ'') ref ref ref)
  (λ ε'' ε⇒ε'' → _ ,p univ⊃*univ ,p uu-redex-red δ δ' ε ε' ref ref ref ref ref ref (inc ε⇒ε'') ref) -}

postulate pre-confluent-case₅ : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ' ε ε' P} → univ φ' ψ' δ' ε' ⇒ P →
                              Σ[ Q ∈ Path V ] R -imp* (univ φ ψ δ ε ∷ P ∷ []) Q × uu-redex φ φ' ψ ψ' δ δ' ε ε' ↠ Q
{-univ-osrE
  {C = λ P → Σ[ Q ∈ Path V ] R -imp* (univ φ ψ δ ε ∷ P ∷ []) Q × uu-redex φ φ' ψ ψ' δ δ' ε ε' ↠ Q}
  (λ φ'' φ'⇒φ'' → _ ,p univ⊃*univ ,p uu-redex-red δ δ' ε ε' ref (inc φ'⇒φ'') ref ref ref ref ref ref)
  (λ ψ'' ψ'⇒ψ'' → _ ,p (univ⊃*univ ,p uu-redex-red δ δ' ε ε' ref ref ref (inc ψ'⇒ψ'') ref ref ref ref)) 
  (λ δ'' δ'⇒δ'' → _ ,p (univ⊃*univ ,p (uu-redex-red δ δ' ε ε' ref ref ref ref ref (inc δ'⇒δ'') ref ref))) 
  (λ ε'' ε'⇒ε'' → _ ,p (univ⊃*univ ,p (uu-redex-red δ δ' ε ε' ref ref ref ref ref ref ref (inc ε'⇒ε'')))) 
  univδε⇒P-}

pre-confluent : ∀ {V} {K} {C} {c : Con (SK C K)} {E E' : ListAbs V C} {F} →
                R c E F → E ⇒ E' → Σ[ F' ∈ Expression V K ] R c E' F' × F ↠ F'
pre-confluent βT (appl (redex ()))
pre-confluent βT (appl (app (appl E⇒E'))) = _ ,p βT ,p red-subl (inc E⇒E')
pre-confluent βT (appl (app (appr ())))
pre-confluent (βT {M = M}) (appr (appl E⇒E')) = _ ,p βT ,p red-subr M (botsub-red E⇒E')
pre-confluent βT (appr (appr ()))
pre-confluent βR (appl (redex ()))
pre-confluent βR (appl (app (appl _))) = _ ,p βR ,p ref
pre-confluent βR (appl (app (appr (appl E⇒E')))) = _ ,p βR ,p red-subl (inc E⇒E')
pre-confluent βR (appl (app (appr (appr ()))))
pre-confluent (βR {δ = δ}) (appr (appl E⇒E')) = _ ,p βR ,p red-subr δ (botsub-red E⇒E')
pre-confluent βR (appr (appr ()))
pre-confluent plus-ref (appl (redex ()))
pre-confluent plus-ref (appl (app (appl E⇒E'))) = _ ,p plus-ref ,p inc (app (appl E⇒E'))
pre-confluent plus-ref (appl (app (appr ())))
pre-confluent plus-ref (appr ())
pre-confluent minus-ref (appl (redex ()))
pre-confluent minus-ref (appl (app (appl E⇒E'))) = _ ,p minus-ref ,p inc (app (appl E⇒E'))
pre-confluent minus-ref (appl (app (appr ())))
pre-confluent minus-ref (appr ())
pre-confluent plus-univ (appl (redex ()))
pre-confluent plus-univ (appl (app (appl _))) = _ ,p plus-univ ,p ref
pre-confluent plus-univ (appl (app (appr (appl _)))) = _ ,p plus-univ ,p ref
pre-confluent plus-univ (appl (app (appr (appr (appl E⇒E'))))) = _ ,p plus-univ ,p inc E⇒E'
pre-confluent plus-univ (appl (app (appr (appr (appr (appl _)))))) = _ ,p plus-univ ,p ref
pre-confluent plus-univ (appl (app (appr (appr (appr (appr ()))))))
pre-confluent plus-univ (appr ())
pre-confluent minus-univ (appl (redex ()))
pre-confluent minus-univ (appl (app (appl _))) = _ ,p minus-univ ,p ref
pre-confluent minus-univ (appl (app (appr (appl _)))) = _ ,p minus-univ ,p ref
pre-confluent minus-univ (appl (app (appr (appr (appl _))))) = _ ,p minus-univ ,p ref
pre-confluent minus-univ (appl (app (appr (appr (appr (appl E⇒E')))))) = _ ,p minus-univ ,p inc E⇒E'
pre-confluent minus-univ (appl (app (appr (appr (appr (appr ()))))))
pre-confluent minus-univ (appr ())
pre-confluent ref⊃*univ (appl (redex ()))
pre-confluent ref⊃*univ (appl (app (appl φ⇒φ'))) = pre-confluent-case₂ φ⇒φ'
pre-confluent ref⊃*univ (appl (app (appr ())))
pre-confluent ref⊃*univ (appr (appl univδε⇒P')) = pre-confluent-case₁ univδε⇒P'
pre-confluent ref⊃*univ (appr (appr ()))
pre-confluent univ⊃*ref (appl univδε⇒P') = pre-confluent-case₃ univδε⇒P'
pre-confluent univ⊃*ref (appr (appl (redex ())))
pre-confluent (univ⊃*ref {δ = δ} {ε}) (appr (appl (app (appl χ⇒χ')))) = _ ,p univ⊃*ref ,p ur-redex-red δ δ ε ε ref ref (inc χ⇒χ') ref ref
pre-confluent univ⊃*ref (appr (appl (app (appr ()))))
pre-confluent univ⊃*ref (appr (appr ()))
pre-confluent {V} (univ⊃*univ {φ = φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'}) (appl univδε⇒P) = pre-confluent-case₄ univδε⇒P
pre-confluent {V} (univ⊃*univ {φ = φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'}) (appr (appl univδε⇒P)) = pre-confluent-case₅ univδε⇒P
pre-confluent univ⊃*univ (appr (appr ()))
pre-confluent ref⊃*ref (appl (redex ()))
pre-confluent ref⊃*ref (appl (app (appl φ⇒φ'))) = _ ,p ref⊃*ref ,p inc (app (appl (app (appl φ⇒φ'))))
pre-confluent ref⊃*ref (appl (app (appr ())))
pre-confluent ref⊃*ref (appr (appl (redex ())))
pre-confluent ref⊃*ref (appr (appl (app E⇒E'))) = {!!}
pre-confluent ref⊃*ref (appr (appr E⇒E')) = {!!}
pre-confluent refref E⇒E' = {!!}
pre-confluent βE E⇒E' = {!!}
pre-confluent (reflamvar {M = M}) (appl N⇒N') = _ ,p reflamvar ,p red-pathsub-endl M (botsub-red N⇒N')
pre-confluent (reflamvar {M = M}) (appr (appl N'⇒N₁')) = _ ,p reflamvar ,p red-pathsub-endr M (botsub-red N'⇒N₁')
pre-confluent reflamvar (appr (appr (appl (redex ()))))
pre-confluent reflamvar (appr (appr (appl (app (appl (redex ()))))))
pre-confluent reflamvar (appr (appr (appl (app (appl (app (appl M⇒M'))))))) = {!!} ,p reflamvar ,p red-pathsub {!!} {!!}
pre-confluent reflamvar (appr (appr (appl (app (appl (app (appr E⇒E'))))))) = {!!}
pre-confluent reflamvar (appr (appr (appl (app (appr E⇒E'))))) = {!!}
pre-confluent reflamvar (appr (appr (appr E⇒E'))) = {!!}
pre-confluent reflam⊃* E⇒E' = {!!}
pre-confluent reflamuniv E⇒E' = {!!}
pre-confluent reflamλλλ E⇒E' = {!!}
\end{code}
}

\begin{prop}
If $r \rightarrow s$ and $r \rightarrow s'$ then there exists $t$ such that $s \rightarrow^? t$ and $s' \rightarrow^? t$.
\end{prop}

\begin{proof}
Case analysis on $r \rightarrow s$ and $r \rightarrow s'$.  There are no critical pairs thanks to our restriction that, if $s \rhd t$, then all proper subterms of $s$ are normal forms; thus, redexes
cannot overlap.
\end{proof}

\begin{cor}[Confluence]
\label{cor:confluence}
$ $
\begin{enumerate}
\item
The reduction relation is confluent: if $r \twoheadrightarrow s$ and $r \twoheadrightarrow s'$, then there exists $t$ such that $s \twoheadrightarrow t$ and $s' \twoheadrightarrow t$.
\item
If $r \simeq s$, then there exists $t$ such that $r \twoheadrightarrow t$ and $s \twoheadrightarrow t$.
\end{enumerate}
\end{cor}

%<*Local-Confluent>
\begin{code}
postulate Local-Confluent : ∀ {V} {C} {K} 
                          {E F G : Subexp V C K} → E ⇒ F → E ⇒ G → 
                            Σ[ H ∈ Subexp V C K ] (F ↠ H × G ↠ H)
\end{code}
%</Local-Confluent>

\AgdaHide{
\begin{code}
{- Local-Confluent (redex x) (redex y) = Critical-Pairs x y
Local-Confluent (redex r) (app E⇒G) = let (H ,p r⇒H ,p G↠H) = pre-confluent r E⇒G in 
  H ,p G↠H ,p inc (redex r⇒H)
Local-Confluent (app E⇒F) (redex r) = let (H ,p r⇒H ,p G↠H) = pre-confluent r E⇒F in 
  H ,p inc (redex r⇒H) ,p G↠H
Local-Confluent (app E⇒F) (app E⇒G) = let (H ,p F↠H ,p G↠H) = Local-Confluent E⇒F E⇒G in 
  app _ H ,p respects-red app F↠H ,p respects-red app G↠H
Local-Confluent (appl E⇒F) (appl E⇒G) = let (H ,p F↠H ,p G↠H) = Local-Confluent E⇒F E⇒G in 
  (H ∷ _) ,p respects-red appl F↠H ,p respects-red appl G↠H
Local-Confluent (appl {E' = E'} E⇒F) (appr {F' = F'} E⇒G) = (E' ∷ F') ,p inc (appr E⇒G) ,p inc (appl E⇒F)
Local-Confluent (appr {F' = F'} E⇒F) (appl {E' = E'} E⇒G) = E' ∷ F' ,p (inc (appl E⇒G)) ,p (inc (appr E⇒F))
Local-Confluent (appr E⇒F) (appr E⇒G) = let (H ,p F↠H ,p G↠H) = Local-Confluent E⇒F E⇒G in
  (_ ∷ H) ,p respects-red appr F↠H ,p respects-red appr G↠H -}
{-Local-Confluent (redex βT) (redex βT) = _ ,p ref ,p ref
Local-Confluent (redex βT) (app (appl (redex ())))
Local-Confluent (redex (βT {M = M} {N})) (app (appl (app (appl {E' = M'} M⇒M')))) = 
  M' ⟦ x₀:= N ⟧ ,p (red-subl (inc M⇒M')) ,p (inc (redex βT))
Local-Confluent (redex βT) (app (appl (app (appr ()))))
Local-Confluent (redex (βT {M = M})) (app (appr (appl {E' = N'} N⇒N'))) =
  M ⟦ x₀:= N' ⟧ ,p red-subr M (botsub-red N⇒N') ,p 
  (inc (redex βT))
Local-Confluent (redex βT) (app (appr (appr ())))
Local-Confluent (redex βR) (redex βR) = _ ,p ref ,p ref
Local-Confluent (redex βR) (app (appl (redex ())))
Local-Confluent (redex βR) (app (appl (app (appl ψ⇒ψ')))) = _ ,p ref ,p (inc (redex βR))
Local-Confluent (redex (βR {δ = δ} {ε = ε})) 
  (app (appl (app (appr (appl {E' = δ'} δ⇒δ'))))) = 
  δ' ⟦ x₀:= ε ⟧ ,p red-subl (inc δ⇒δ') ,p inc (redex βR)
Local-Confluent (redex βR) (app (appl (app (appr (appr ())))))
Local-Confluent (redex (βR {δ = δ})) (app (appr (appl {E' = ε'} ε⇒ε'))) = 
  δ ⟦ x₀:= ε' ⟧ ,p red-subr δ (botsub-red ε⇒ε') ,p inc (redex βR)
Local-Confluent (redex βR) (app (appr (appr ())))
Local-Confluent (redex βE) (redex βE) = _ ,p ref ,p ref
Local-Confluent (redex (βE {N = N} {A = A} {P = P} {Q = Q})) (app (appl {E' = M'} M⇒M')) = 
  P ⟦ x₂:= M' ,x₁:= N ,x₀:= Q ⟧ ,p red-subr P (botsub₃-red (inc M⇒M') ref ref) ,p inc (redex βE)
Local-Confluent (redex (βE {M = M} {P = P} {Q = Q})) (app (appr (appl {E' = N'} N⇒N'))) = 
  P ⟦ x₂:= M ,x₁:= N' ,x₀:= Q ⟧ ,p (red-subr P (botsub₃-red ref (inc N⇒N') ref)) ,p 
  inc (redex βE)
Local-Confluent (redex βE) (app (appr (appr (appl (redex ())))))
Local-Confluent (redex (βE {M = M} {N = N} {Q = Q})) (app (appr (appr (appl (app (appl {E' = P'} P⇒P')))))) = P' ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧ ,p (red-subl (inc P⇒P')) ,p inc (redex βE)
Local-Confluent (redex βE) (app (appr (appr (appl (app (appr ()))))))
Local-Confluent (redex (βE {M = M} {N = N} {P = P})) (app (appr (appr (appr (appl {E' = Q'} Q⇒Q'))))) = P ⟦ x₂:= M ,x₁:= N ,x₀:= Q' ⟧ ,p (red-subr P (botsub₃-red ref ref (inc Q⇒Q'))) ,p (inc (redex βE))
Local-Confluent (redex βE) (app (appr (appr (appr (appr ())))))
Local-Confluent (redex plus-ref) (redex plus-ref) = _ ,p (ref ,p ref)
Local-Confluent (redex plus-ref) (app (appl (redex ())))
Local-Confluent (redex plus-ref) (app (appl (app (appl {E' = ψ'} ψ⇒ψ')))) = ΛP ψ' (var x₀)  ,p (inc (app (appl ψ⇒ψ'))) ,p (inc (redex plus-ref))
Local-Confluent (redex plus-ref) (app (appl (app (appr ()))))
Local-Confluent (redex plus-ref) (app (appr ()))
Local-Confluent (redex minus-ref) (redex minus-ref) = _ ,p ref ,p ref
Local-Confluent (redex minus-ref) (app (appl (redex ())))
Local-Confluent (redex minus-ref) (app (appl (app (appl {E' = ψ'} ψ⇒ψ')))) = ΛP ψ' (var x₀) ,p (inc (app (appl ψ⇒ψ'))) ,p (inc (redex minus-ref))
Local-Confluent (redex minus-ref) (app (appl (app (appr ()))))
Local-Confluent (redex minus-ref) (app (appr ()))
Local-Confluent (redex plus-univ) (redex plus-univ) = _ ,p ref ,p ref
Local-Confluent (redex plus-univ) (app (appl (redex ())))
Local-Confluent (redex plus-univ) (app (appl (app (appl _)))) = 
  _ ,p ref ,p inc (redex plus-univ)
Local-Confluent (redex plus-univ) (app (appl (app (appr (appl _))))) = 
  _ ,p ref ,p (inc (redex plus-univ))
Local-Confluent (redex plus-univ) (app (appl (app (appr (appr (appl δ⇒δ')))))) = 
  _ ,p inc δ⇒δ' ,p inc (redex plus-univ)
Local-Confluent (redex plus-univ) (app (appl (app (appr (appr (appr (appl E⇒G))))))) = 
  _ ,p ref ,p inc (redex plus-univ)
Local-Confluent (redex plus-univ) (app (appl (app (appr (appr (appr (appr ())))))))
Local-Confluent (redex plus-univ) (app (appr ()))
Local-Confluent (redex minus-univ) (redex minus-univ) = _ ,p ref ,p ref
Local-Confluent (redex minus-univ) (app (appl (redex ())))
Local-Confluent (redex minus-univ) (app (appl (app (appl _)))) = 
  _ ,p ref ,p inc (redex minus-univ)
Local-Confluent (redex minus-univ) (app (appl (app (appr (appl _))))) = 
  _ ,p ref ,p (inc (redex minus-univ))
Local-Confluent (redex minus-univ) (app (appl (app (appr (appr (appl _)))))) = 
  _ ,p ref ,p inc (redex minus-univ)
Local-Confluent (redex minus-univ) (app (appl (app (appr (appr (appr (appl ε⇒ε'))))))) = 
  _ ,p inc ε⇒ε' ,p inc (redex minus-univ)
Local-Confluent (redex minus-univ) (app (appl (app (appr (appr (appr (appr ())))))))
Local-Confluent (redex minus-univ) (app (appr ()))
Local-Confluent (redex ref⊃*univ) (redex ref⊃*univ) = 
  _ ,p ref ,p ref
Local-Confluent (redex ref⊃*univ) (app (appl (redex ())))
Local-Confluent (redex ref⊃*univ) (app (appl (app (appl ψ⇒ψ')))) = 
  _ ,p univ-red (inc (app (appl ψ⇒ψ'))) (inc (app (appl ψ⇒ψ'))) 
    (ΛP-red (inc (app (appl ψ⇒ψ'))) (ΛP-red (apredr replacement R-respects-replacement (inc ψ⇒ψ')) ref)) (ΛP-red (inc (app (appl ψ⇒ψ'))) (ΛP-red (apredr replacement R-respects-replacement (inc ψ⇒ψ')) ref)) ,p inc (redex ref⊃*univ)
Local-Confluent (redex ref⊃*univ) (app (appl (app (appr ()))))
Local-Confluent (redex ref⊃*univ) (app (appr (appl E⇒G))) = {!!}
Local-Confluent (redex ref⊃*univ) (app (appr (appr E⇒G))) = {!!}
Local-Confluent (redex univ⊃*ref) E⇒G = {!!}
Local-Confluent (redex univ⊃*univ) E⇒G = {!!}
Local-Confluent (redex ref⊃*ref) E⇒G = {!!}
Local-Confluent (redex refref) E⇒G = {!!}
Local-Confluent (redex reflamvar) E⇒G = {!!}
Local-Confluent (redex reflam⊃*) E⇒G = {!!}
Local-Confluent (redex reflamuniv) E⇒G = {!!}
Local-Confluent (redex reflamλλλ) E⇒G = {!!}
Local-Confluent (app E⇒F) E⇒G = {!!} -}
--TODO General theory of reduction
\end{code}
}

\begin{code}
postulate Newmans : ∀ {V} {C} {K} {E F G : Subexp V C K} → 
                  SN E → (E ↠ F) → (E ↠ G) →
                  Σ[ H ∈ Subexp V C K ] (F ↠ H × G ↠ H)

postulate ChurchRosserT : ∀ {V} {M N P : Term V} → M ↠ N → M ↠ P →
                        Σ[ Q ∈ Term V ] N ↠ Q × P ↠ Q

postulate confluenceT : ∀ {V} {M N : Term V} → M ≃ N →
                        Σ[ Q ∈ Term V ] M ↠ Q × N ↠ Q

\end{code}
}
