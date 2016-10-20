\AgdaHide{
\begin{code}
module PHOPL.Red.Confluent where
open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Red

postulate Critical-Pairs : ∀ {V} {K} {C} {c : Constructor (SK C K)} {E : ListAbs V C} {F} {G} → R c E F → R c E G → Σ[ H ∈ Expression V K ] ((F ↠ H) × (G ↠ H))
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
{- pre-confluent-case₁ {V} {φ} {ψ} {χ} {δ} {ε} {P} = univ-osrE 
    {C = λ P → Σ[ Q ∈ Path V ] R -imp* (reff φ ∷ P ∷ []) Q × ru-redex φ ψ χ δ ε ↠ Q}
    (λ ψ' ψ⇒ψ' → _ ,p ref⊃*univ ,p univ-red (osr-red (app (appr (appl ψ⇒ψ')))) ref (osr-red (app (appl (app (appr (appl ψ⇒ψ')))))) ref)
    (λ χ' χ⇒χ' → _ ,p ref⊃*univ ,p univ-red ref (osr-red (app (appr (appl χ⇒χ')))) ref (osr-red (app (appl (app (appr (appl χ⇒χ'))))))) 
    (λ δ' δ⇒δ' → _ ,p ref⊃*univ ,p osr-red (app (appr (appr (appl (app (appr (appl (app (appr (appl (app (appl 
      (osr-rep (osr-rep δ⇒δ'))))))))))))))) 
    (λ ε' ε⇒ε' → _ ,p ref⊃*univ ,p osr-red (app (appr (appr (appr (appl (app (appr (appl (app (appr (appl (app (appl 
      (osr-rep (osr-rep ε⇒ε')))))))))))))))) -}

postulate pre-confluent-case₂ : ∀ {V φ φ' ψ χ δ ε} → φ ⇒ φ' → Σ[ Q ∈ Path V ] R -imp* (reff φ' ∷ univ ψ χ δ ε ∷ []) Q × ru-redex φ ψ χ δ ε ↠ Q
{- pre-confluent-case₂ {V} {φ} {φ'} {ψ} {χ} {δ} {ε} φ⇒φ' = 
  let φ⊃θ↠φ'⊃θ : ∀ θ → φ ⊃ θ ↠ φ' ⊃ θ
      φ⊃θ↠φ'⊃θ _ = osr-red (app (appl φ⇒φ')) in
  let λφ↠λφ' : ∀ θ δ → ΛP (φ ⊃ θ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀)))) ↠ ΛP (φ' ⊃ θ) (ΛP (φ' ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))
      λφ↠λφ' _ _ = ΛP-red (φ⊃θ↠φ'⊃θ _) (osr-red (app (appl (respects-osr REP R-respects-replacement φ⇒φ')))) in
  _ ,p ref⊃*univ ,p univ-red (φ⊃θ↠φ'⊃θ _) (φ⊃θ↠φ'⊃θ _) (λφ↠λφ' _ δ) (λφ↠λφ' _ ε) -}

postulate pre-confluent-case₃ : ∀ {V φ ψ χ δ ε P} → univ φ ψ δ ε ⇒ P → Σ[ Q ∈ Path V ] R -imp* (P ∷ reff χ ∷ []) Q × ur-redex φ ψ χ δ ε ↠ Q
{- pre-confluent-case₃ {V} {φ} {ψ} {χ} {δ} {ε} {P} = univ-osrE
  {C = λ P → Σ-syntax (Path V) (λ Q →
    R -imp* (P ∷ reff χ ∷ []) Q × ur-redex φ ψ χ δ ε ↠ Q)}
  (λ φ' φ⇒φ' → _ ,p univ⊃*ref ,p univ-red (osr-red (app (appl φ⇒φ'))) ref (osr-red (app (appl (app (appl φ⇒φ'))))) (osr-red (app (appr (appl (app (appl (osr-rep φ⇒φ')))))))) 
  (λ ψ' ψ⇒ψ' → _ ,p univ⊃*ref ,p (univ-red ref (osr-red (app (appl ψ⇒ψ'))) (osr-red (app (appr (appl (app (appl (osr-rep ψ⇒ψ'))))))) (osr-red (app (appl (app (appl ψ⇒ψ'))))))) 
  (λ δ' δ⇒δ' → _ ,p (univ⊃*ref ,p (osr-red (app (appr (appr (appr (appl (app (appr (appl (app (appr (appl (app (appr (appl (app (appl (osr-rep (osr-rep δ⇒δ'))))))))))))))))))))) 
  (λ ε' ε⇒ε' → _ ,p univ⊃*ref ,p (osr-red (app (appr (appr (appl (app (appr (appl (app (appr (appl (app (appr (appl (app (appl (osr-rep (osr-rep ε⇒ε'))))))))))))))))))) -}

pre-confluent : ∀ {V} {K} {C} {c : Constructor (SK C K)} {E E' : ListAbs V C} {F} →
                        R c E F → E ⇒ E' → Σ[ F' ∈ Expression V K ] R c E' F' × F ↠ F'
pre-confluent βT (appl (redex ()))
pre-confluent βT (appl (app (appl E⇒E'))) = _ ,p βT ,p red-subl (osr-red E⇒E')
pre-confluent βT (appl (app (appr ())))
pre-confluent (βT {M = M}) (appr (appl E⇒E')) = _ ,p βT ,p red-subr M (botsub-red E⇒E')
pre-confluent βT (appr (appr ()))
pre-confluent βR (appl (redex ()))
pre-confluent βR (appl (app (appl _))) = _ ,p βR ,p ref
pre-confluent βR (appl (app (appr (appl E⇒E')))) = _ ,p βR ,p red-subl (osr-red E⇒E')
pre-confluent βR (appl (app (appr (appr ()))))
pre-confluent (βR {δ = δ}) (appr (appl E⇒E')) = _ ,p βR ,p red-subr δ (botsub-red E⇒E')
pre-confluent βR (appr (appr ()))
pre-confluent plus-ref (appl (redex ()))
pre-confluent plus-ref (appl (app (appl E⇒E'))) = _ ,p plus-ref ,p osr-red (app (appl E⇒E'))
pre-confluent plus-ref (appl (app (appr ())))
pre-confluent plus-ref (appr ())
pre-confluent minus-ref (appl (redex ()))
pre-confluent minus-ref (appl (app (appl E⇒E'))) = _ ,p minus-ref ,p osr-red (app (appl E⇒E'))
pre-confluent minus-ref (appl (app (appr ())))
pre-confluent minus-ref (appr ())
pre-confluent plus-univ (appl (redex ()))
pre-confluent plus-univ (appl (app (appl _))) = _ ,p plus-univ ,p ref
pre-confluent plus-univ (appl (app (appr (appl _)))) = _ ,p plus-univ ,p ref
pre-confluent plus-univ (appl (app (appr (appr (appl E⇒E'))))) = _ ,p plus-univ ,p osr-red E⇒E'
pre-confluent plus-univ (appl (app (appr (appr (appr (appl _)))))) = _ ,p plus-univ ,p ref
pre-confluent plus-univ (appl (app (appr (appr (appr (appr ()))))))
pre-confluent plus-univ (appr ())
pre-confluent minus-univ (appl (redex ()))
pre-confluent minus-univ (appl (app (appl _))) = _ ,p minus-univ ,p ref
pre-confluent minus-univ (appl (app (appr (appl _)))) = _ ,p minus-univ ,p ref
pre-confluent minus-univ (appl (app (appr (appr (appl _))))) = _ ,p minus-univ ,p ref
pre-confluent minus-univ (appl (app (appr (appr (appr (appl E⇒E')))))) = _ ,p minus-univ ,p osr-red E⇒E'
pre-confluent minus-univ (appl (app (appr (appr (appr (appr ()))))))
pre-confluent minus-univ (appr ())
pre-confluent ref⊃*univ (appl (redex ()))
pre-confluent (ref⊃*univ {φ = φ} {ψ = ψ} {χ = χ} {δ = δ} {ε = ε}) (appl (app (appl {E' = φ'} φ⇒φ'))) = pre-confluent-case₂ φ⇒φ'
pre-confluent ref⊃*univ (appl (app (appr ())))
pre-confluent {V = V} (ref⊃*univ {φ = φ} {ψ = ψ} {χ = χ} {δ = δ} {ε = ε}) (appr (appl {E' = P'} univδε⇒P')) = pre-confluent-case₁ univδε⇒P'
pre-confluent ref⊃*univ (appr (appr ()))
pre-confluent {V} (univ⊃*ref {φ = φ} {ψ} {χ} {δ} {ε}) (appl univδε⇒P') = pre-confluent-case₃ univδε⇒P'
pre-confluent univ⊃*ref (appr (appl (redex ())))
pre-confluent univ⊃*ref (appr (appl (app (appl χ⇒χ')))) = _ ,p univ⊃*ref ,p univ-red (osr-red (app (appr (appl χ⇒χ')))) (osr-red (app (appr (appl χ⇒χ')))) 
  (osr-red (app (appl (app (appr (appl χ⇒χ')))))) (osr-red (app (appl (app (appr (appl χ⇒χ'))))))
pre-confluent univ⊃*ref (appr (appl (app (appr ()))))
pre-confluent univ⊃*ref (appr (appr ()))
pre-confluent {V} (univ⊃*univ {φ = φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'}) (appl univδε⇒P) = univ-osrE
  {C = λ P → Σ-syntax (Path V)
    (λ Q → R -imp* (P ∷ univ φ' ψ' δ' ε' ∷ []) Q ×
      (uu-redex φ φ' ψ ψ' δ δ' ε ε' ↠ Q))}
  (λ φ'' φ⇒φ'' → _ ,p univ⊃*univ ,p univ-red (osr-red (app (appl φ⇒φ''))) ref (osr-red (app (appl (app (appl φ⇒φ''))))) 
    (osr-red (app (appr (appl (app (appl (osr-rep φ⇒φ'')))))))) 
  (λ ψ'' ψ⇒ψ'' → _ ,p univ⊃*univ ,p univ-red ref (osr-red (app (appl ψ⇒ψ''))) (osr-red (app (appr (appl (app (appl (osr-rep ψ⇒ψ''))))))) 
    (osr-red (app (appl (app (appl ψ⇒ψ'')))))) 
  (λ δ'' δ⇒δ'' → _ ,p univ⊃*univ ,p univ-red ref ref ref (osr-red (app (appr (appl (app (appr (appl (app (appr (appl (app (appr (appl (app (appl (osr-rep (osr-rep δ⇒δ'')))))))))))))))))) 
  (λ ε'' ε⇒ε'' → _ ,p univ⊃*univ ,p univ-red ref ref (osr-red (app (appr (appl (app (appr (appl (app (appr (appl (app (appr (appl (app (appl (osr-rep (osr-rep ε⇒ε''))))))))))))))))) ref) 
  univδε⇒P
pre-confluent {V} (univ⊃*univ {φ = φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'}) (appr (appl univδε⇒P)) = univ-osrE
                                                                                              {C =
                                                                                               λ P →
                                                                                                 Σ-syntax (Path V)
                                                                                                 (λ Q →
                                                                                                    R -imp* (univ φ ψ δ ε ∷ P ∷ []) Q ×
                                                                                                    (uu-redex φ φ' ψ ψ' δ δ' ε ε' ↠ Q))}
              (λ φ'' φ'⇒φ'' → _ ,p univ⊃*univ ,p univ-red (osr-red (app (appr (appl φ'⇒φ'')))) ref (osr-red (app (appl (app (appr (appl φ'⇒φ'')))))) {!!}) {!!} {!!} {!!} univδε⇒P
pre-confluent univ⊃*univ (appr (appr E⇒E')) = {!!}
pre-confluent ref⊃*ref E⇒E' = {!!}
pre-confluent refref E⇒E' = {!!}
pre-confluent βE E⇒E' = {!!}
pre-confluent reflamvar E⇒E' = {!!}
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
                          {E F G : Subexpression V C K} → E ⇒ F → E ⇒ G → 
                            Σ[ H ∈ Subexpression V C K ] (F ↠ H × G ↠ H)
\end{code}
%</Local-Confluent>

\AgdaHide{
\begin{code}
{- Local-Confluent (redex x) (redex y) = Critical-Pairs x y
Local-Confluent (redex r) (app E⇒G) = let (H ,p r⇒H ,p G↠H) = pre-confluent r E⇒G in 
  H ,p G↠H ,p osr-red (redex r⇒H)
Local-Confluent (app E⇒F) (redex r) = let (H ,p r⇒H ,p G↠H) = pre-confluent r E⇒F in 
  H ,p osr-red (redex r⇒H) ,p G↠H
Local-Confluent (app E⇒F) (app E⇒G) = let (H ,p F↠H ,p G↠H) = Local-Confluent E⇒F E⇒G in 
  app _ H ,p respects-red app F↠H ,p respects-red app G↠H
Local-Confluent (appl E⇒F) (appl E⇒G) = let (H ,p F↠H ,p G↠H) = Local-Confluent E⇒F E⇒G in 
  (H ∷ _) ,p respects-red appl F↠H ,p respects-red appl G↠H
Local-Confluent (appl {E' = E'} E⇒F) (appr {F' = F'} E⇒G) = (E' ∷ F') ,p osr-red (appr E⇒G) ,p osr-red (appl E⇒F)
Local-Confluent (appr {F' = F'} E⇒F) (appl {E' = E'} E⇒G) = E' ∷ F' ,p (osr-red (appl E⇒G)) ,p (osr-red (appr E⇒F))
Local-Confluent (appr E⇒F) (appr E⇒G) = let (H ,p F↠H ,p G↠H) = Local-Confluent E⇒F E⇒G in
  (_ ∷ H) ,p respects-red appr F↠H ,p respects-red appr G↠H -}
{-Local-Confluent (redex βT) (redex βT) = _ ,p ref ,p ref
Local-Confluent (redex βT) (app (appl (redex ())))
Local-Confluent (redex (βT {M = M} {N})) (app (appl (app (appl {E' = M'} M⇒M')))) = 
  M' ⟦ x₀:= N ⟧ ,p (red-subl (osr-red M⇒M')) ,p (osr-red (redex βT))
Local-Confluent (redex βT) (app (appl (app (appr ()))))
Local-Confluent (redex (βT {M = M})) (app (appr (appl {E' = N'} N⇒N'))) =
  M ⟦ x₀:= N' ⟧ ,p red-subr M (botsub-red N⇒N') ,p 
  (osr-red (redex βT))
Local-Confluent (redex βT) (app (appr (appr ())))
Local-Confluent (redex βR) (redex βR) = _ ,p ref ,p ref
Local-Confluent (redex βR) (app (appl (redex ())))
Local-Confluent (redex βR) (app (appl (app (appl ψ⇒ψ')))) = _ ,p ref ,p (osr-red (redex βR))
Local-Confluent (redex (βR {δ = δ} {ε = ε})) 
  (app (appl (app (appr (appl {E' = δ'} δ⇒δ'))))) = 
  δ' ⟦ x₀:= ε ⟧ ,p red-subl (osr-red δ⇒δ') ,p osr-red (redex βR)
Local-Confluent (redex βR) (app (appl (app (appr (appr ())))))
Local-Confluent (redex (βR {δ = δ})) (app (appr (appl {E' = ε'} ε⇒ε'))) = 
  δ ⟦ x₀:= ε' ⟧ ,p red-subr δ (botsub-red ε⇒ε') ,p osr-red (redex βR)
Local-Confluent (redex βR) (app (appr (appr ())))
Local-Confluent (redex βE) (redex βE) = _ ,p ref ,p ref
Local-Confluent (redex (βE {N = N} {A = A} {P = P} {Q = Q})) (app (appl {E' = M'} M⇒M')) = 
  P ⟦ x₂:= M' ,x₁:= N ,x₀:= Q ⟧ ,p red-subr P (botsub₃-red (osr-red M⇒M') ref ref) ,p osr-red (redex βE)
Local-Confluent (redex (βE {M = M} {P = P} {Q = Q})) (app (appr (appl {E' = N'} N⇒N'))) = 
  P ⟦ x₂:= M ,x₁:= N' ,x₀:= Q ⟧ ,p (red-subr P (botsub₃-red ref (osr-red N⇒N') ref)) ,p 
  osr-red (redex βE)
Local-Confluent (redex βE) (app (appr (appr (appl (redex ())))))
Local-Confluent (redex (βE {M = M} {N = N} {Q = Q})) (app (appr (appr (appl (app (appl {E' = P'} P⇒P')))))) = P' ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧ ,p (red-subl (osr-red P⇒P')) ,p osr-red (redex βE)
Local-Confluent (redex βE) (app (appr (appr (appl (app (appr ()))))))
Local-Confluent (redex (βE {M = M} {N = N} {P = P})) (app (appr (appr (appr (appl {E' = Q'} Q⇒Q'))))) = P ⟦ x₂:= M ,x₁:= N ,x₀:= Q' ⟧ ,p (red-subr P (botsub₃-red ref ref (osr-red Q⇒Q'))) ,p (osr-red (redex βE))
Local-Confluent (redex βE) (app (appr (appr (appr (appr ())))))
Local-Confluent (redex plus-ref) (redex plus-ref) = _ ,p (ref ,p ref)
Local-Confluent (redex plus-ref) (app (appl (redex ())))
Local-Confluent (redex plus-ref) (app (appl (app (appl {E' = ψ'} ψ⇒ψ')))) = ΛP ψ' (var x₀)  ,p (osr-red (app (appl ψ⇒ψ'))) ,p (osr-red (redex plus-ref))
Local-Confluent (redex plus-ref) (app (appl (app (appr ()))))
Local-Confluent (redex plus-ref) (app (appr ()))
Local-Confluent (redex minus-ref) (redex minus-ref) = _ ,p ref ,p ref
Local-Confluent (redex minus-ref) (app (appl (redex ())))
Local-Confluent (redex minus-ref) (app (appl (app (appl {E' = ψ'} ψ⇒ψ')))) = ΛP ψ' (var x₀) ,p (osr-red (app (appl ψ⇒ψ'))) ,p (osr-red (redex minus-ref))
Local-Confluent (redex minus-ref) (app (appl (app (appr ()))))
Local-Confluent (redex minus-ref) (app (appr ()))
Local-Confluent (redex plus-univ) (redex plus-univ) = _ ,p ref ,p ref
Local-Confluent (redex plus-univ) (app (appl (redex ())))
Local-Confluent (redex plus-univ) (app (appl (app (appl _)))) = 
  _ ,p ref ,p osr-red (redex plus-univ)
Local-Confluent (redex plus-univ) (app (appl (app (appr (appl _))))) = 
  _ ,p ref ,p (osr-red (redex plus-univ))
Local-Confluent (redex plus-univ) (app (appl (app (appr (appr (appl δ⇒δ')))))) = 
  _ ,p osr-red δ⇒δ' ,p osr-red (redex plus-univ)
Local-Confluent (redex plus-univ) (app (appl (app (appr (appr (appr (appl E⇒G))))))) = 
  _ ,p ref ,p osr-red (redex plus-univ)
Local-Confluent (redex plus-univ) (app (appl (app (appr (appr (appr (appr ())))))))
Local-Confluent (redex plus-univ) (app (appr ()))
Local-Confluent (redex minus-univ) (redex minus-univ) = _ ,p ref ,p ref
Local-Confluent (redex minus-univ) (app (appl (redex ())))
Local-Confluent (redex minus-univ) (app (appl (app (appl _)))) = 
  _ ,p ref ,p osr-red (redex minus-univ)
Local-Confluent (redex minus-univ) (app (appl (app (appr (appl _))))) = 
  _ ,p ref ,p (osr-red (redex minus-univ))
Local-Confluent (redex minus-univ) (app (appl (app (appr (appr (appl _)))))) = 
  _ ,p ref ,p osr-red (redex minus-univ)
Local-Confluent (redex minus-univ) (app (appl (app (appr (appr (appr (appl ε⇒ε'))))))) = 
  _ ,p osr-red ε⇒ε' ,p osr-red (redex minus-univ)
Local-Confluent (redex minus-univ) (app (appl (app (appr (appr (appr (appr ())))))))
Local-Confluent (redex minus-univ) (app (appr ()))
Local-Confluent (redex ref⊃*univ) (redex ref⊃*univ) = 
  _ ,p ref ,p ref
Local-Confluent (redex ref⊃*univ) (app (appl (redex ())))
Local-Confluent (redex ref⊃*univ) (app (appl (app (appl ψ⇒ψ')))) = 
  _ ,p univ-red (osr-red (app (appl ψ⇒ψ'))) (osr-red (app (appl ψ⇒ψ'))) 
    (ΛP-red (osr-red (app (appl ψ⇒ψ'))) (ΛP-red (apredr replacement R-respects-replacement (osr-red ψ⇒ψ')) ref)) (ΛP-red (osr-red (app (appl ψ⇒ψ'))) (ΛP-red (apredr replacement R-respects-replacement (osr-red ψ⇒ψ')) ref)) ,p osr-red (redex ref⊃*univ)
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
postulate Newmans : ∀ {V} {C} {K} {E F G : Subexpression V C K} → 
                  SN E → (E ↠ F) → (E ↠ G) →
                  Σ[ H ∈ Subexpression V C K ] (F ↠ H × G ↠ H)

postulate ChurchRosserT : ∀ {V} {M N P : Term V} → M ↠ N → M ↠ P →
                        Σ[ Q ∈ Term V ] N ↠ Q × P ↠ Q

postulate confluenceT : ∀ {V} {M N : Term V} → M ≃ N →
                        Σ[ Q ∈ Term V ] M ↠ Q × N ↠ Q

\end{code}
}
