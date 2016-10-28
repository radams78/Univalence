\AgdaHide{
\begin{code}
module PHOPL.Red.Confluent where
open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red
open import Reduction PHOPL β as Redβ
open import Reduction PHOPL R₀ as Red₀
open import Reduction PHOPL R as Red

postulate β-confluent : ∀ {V C K} {E F G : Subexp V C K} → E Redβ.↠ F → E Redβ.↠ G → Σ[ H ∈ Subexp V C K ] F Redβ.↠ H × G Redβ.↠ H

R₀-det : ∀ {V AA K} {c : Con (SK AA K)} {EE : ListAbs V AA} {F G} → R₀ c EE F → app c EE Red.⇒ G → F ≡ G
R₀-det () (Red.redex (βR βT))
R₀-det (βR x x₁) (Red.redex (R₀R (βR x₂ x₃))) = refl
R₀-det (dir-ref x) (Red.redex (R₀R (dir-ref x₁))) = refl
R₀-det (plus-univ x) (Red.redex (R₀R (plus-univ x₁))) = refl
R₀-det (minus-univ x) (Red.redex (R₀R (minus-univ x₁))) = refl
R₀-det (ref⊃*univ x x₁) (Red.redex (R₀R (ref⊃*univ x₂ x₃))) = refl
R₀-det (univ⊃*ref x x₁) (Red.redex (R₀R (univ⊃*ref x₂ x₃))) = refl
R₀-det (univ⊃*univ x x₁) (Red.redex (R₀R (univ⊃*univ x₂ x₃))) = refl
R₀-det (ref⊃*ref x x₁) (Red.redex (R₀R (ref⊃*ref x₂ x₃))) = refl
R₀-det (refref x x₁) (Red.redex (R₀R (refref x₂ x₃))) = refl
R₀-det (refref x x₁) (Red.redex (R₀R (reflam x₂ x₃ x₄ x₅ ())))
R₀-det (βE x x₁ x₂ x₃) (Red.redex (R₀R (βE x₄ x₅ x₆ x₇))) = refl
R₀-det (reflam x x₁ x₂ x₃ ()) (Red.redex (R₀R (refref x₅ x₆)))
R₀-det (reflam x x₁ x₂ x₃ x₄) (Red.redex (R₀R (reflam x₅ x₆ x₇ x₈ x₉))) = refl
R₀-det {K = varKind -Term} () (Red.app _)
R₀-det {K = varKind -Proof} cEE▷F (Red.app cEE⇒G) with nfredexproof cEE▷F cEE⇒G
R₀-det {K = varKind -Proof} cEE▷F (Red.app cEE⇒G) | ()
R₀-det {K = varKind -Path} cEE▷F (Red.app cEE⇒G) with nfredexpath cEE▷F cEE⇒G
R₀-det {K = varKind -Path} cEE▷F (Red.app cEE⇒G) | ()
R₀-det {K = nonVarKind _} () _

R₀-diamond : ∀ {V C K} {E F G : Subexp V C K} → E Red₀.⇒ F → E Red₀.⇒ G → Σ[ H ∈ Subexp V C K ] F Red₀.⇒? H × G Red₀.⇒? H
R₀-diamond {F = F} {G} (Red₀.redex E▷F) E⇒G = F ,p ref ,p subst (λ x → x Red₀.⇒? F) (R₀-det E▷F (R₀-imp-R E⇒G)) ref
R₀-diamond {F = F} {G} E⇒F (Red₀.redex E▷G) = F ,p ref ,p subst (λ x → G Red₀.⇒? x) (R₀-det E▷G (R₀-imp-R E⇒F)) ref
R₀-diamond (Red₀.app {c = c} E⇒F) (Red₀.app E⇒G) = let H ,p F⇒H ,p G⇒H = R₀-diamond E⇒F E⇒G in app c H ,p Red₀.app-resp-red? F⇒H ,p Red₀.app-resp-red? G⇒H
R₀-diamond (Red₀.appl E⇒F) (Red₀.appl E⇒G) = let H ,p F⇒H ,p G⇒H = R₀-diamond E⇒F E⇒G in H ∷ _ ,p Red₀.appl-resp-red? F⇒H ,p Red₀.appl-resp-red? G⇒H
R₀-diamond (Red₀.appl E⇒F) (Red₀.appr E⇒G) = _ ,p Red₀.appr-resp-red? (inc E⇒G) ,p Red₀.appl-resp-red? (inc E⇒F)
R₀-diamond (Red₀.appr E⇒F) (Red₀.appl E⇒G) = _ ,p Red₀.appl-resp-red? (inc E⇒G) ,p Red₀.appr-resp-red? (inc E⇒F)
R₀-diamond (Red₀.appr E⇒F) (Red₀.appr E⇒G) = let H ,p F⇒?H ,p G⇒?H = R₀-diamond E⇒F E⇒G in _ ∷ H ,p Red₀.appr-resp-red? F⇒?H ,p Red₀.appr-resp-red? G⇒?H

R₀-β-diamond : ∀ {V C K} {E F G : Subexp V C K} → E Red₀.⇒ F → E Redβ.⇒ G → Σ[ H ∈ Subexp V C K ] F Redβ.⇒ H × G Red₀.↠ H
R₀-β-diamond (Red₀.redex ()) (Redβ.redex βT)
R₀-β-diamond {K = varKind -Proof} (Red₀.redex E▷F) (Redβ.app E⇒G) with nfredexproof E▷F (β-imp-R E⇒G)
R₀-β-diamond {K = varKind -Proof} (Red₀.redex E▷F) (Redβ.app E⇒G) | ()
R₀-β-diamond {K = varKind -Term} (Red₀.redex ()) (Redβ.app _)
R₀-β-diamond {K = varKind -Path} (Red₀.redex E▷F) (Redβ.app E⇒G) with nfredexpath E▷F (β-imp-R E⇒G)
R₀-β-diamond {K = varKind -Path} (Red₀.redex E▷F) (Redβ.app E⇒G) | ()
R₀-β-diamond {K = nonVarKind _} (Red₀.redex ()) (Redβ.app _)
R₀-β-diamond (Red₀.app (Red₀.appl (Red₀.redex ()))) (Redβ.redex βT)
R₀-β-diamond (Red₀.app (Red₀.appl (Red₀.app (Red₀.appl M⇒M')))) (Redβ.redex βT) = _ ,p Redβ.redex βT ,p Red₀.respects-red (Red₀.aposrr SUB R₀-respects-sub) (inc M⇒M')
R₀-β-diamond (Red₀.app (Red₀.appl (Red₀.app (Red₀.appr ())))) (Redβ.redex βT)
R₀-β-diamond (Red₀.app (Red₀.appr (Red₀.appl N⇒N'))) (Redβ.redex (βT {M = M})) = _ ,p Redβ.redex βT ,p red₀-subr M (Red₀.botsub-red N⇒N')
R₀-β-diamond (Red₀.app (Red₀.appr (Red₀.appr ()))) (Redβ.redex βT)
R₀-β-diamond (Red₀.app EE⇒FF) (Redβ.app EE⇒GG) = let HH ,p FF⇒HH ,p GG↠HH = R₀-β-diamond EE⇒FF EE⇒GG in app _ HH ,p Redβ.app FF⇒HH ,p Red₀.app-resp-red GG↠HH
R₀-β-diamond (Red₀.appl E⇒F) (Redβ.appl E⇒G) = let H ,p F⇒H ,p G↠H = R₀-β-diamond E⇒F E⇒G in H ∷ _ ,p Redβ.appl F⇒H ,p Red₀.appl-resp-red G↠H
R₀-β-diamond (Red₀.appl E⇒F) (Redβ.appr EE⇒GG) = _ ,p Redβ.appr EE⇒GG ,p inc (Red₀.appl E⇒F)
R₀-β-diamond (Red₀.appr EE⇒FF) (Redβ.appl E⇒G) = _ ,p Redβ.appl E⇒G ,p inc (Red₀.appr EE⇒FF)
R₀-β-diamond (Red₀.appr EE⇒FF) (Redβ.appr EE⇒GG) = let HH ,p FF⇒HH ,p GG↠HH = R₀-β-diamond EE⇒FF EE⇒GG in _ ,p Redβ.appr FF⇒HH ,p Red₀.appr-resp-red GG↠HH

{-                R c EE F → app c EE ⇒ G → Σ[ H ∈ Expression V K ] F ↠ H × G ↠ H
confluent▷⇒ {F = F} cEE▷F (redex E▷G) = F ,p ref ,p (subst (λ x → x ↠ F) (R-det cEE▷F E▷G) ref)
confluent▷⇒ {K = varKind -Proof} cEE▷F (app cEE⇒G) with nfredexproof cEE▷F cEE⇒G
confluent▷⇒ {K = varKind -Proof} cEE▷F (app cEE⇒G) | ()
confluent▷⇒ {K = varKind -Term} βT (app (appl (redex ())))
confluent▷⇒ {K = varKind -Term} (βT {N = N}) (app (appl (app (appl {E' = M'} M⇒M')))) = M' ⟦ x₀:= N ⟧ ,p red-subl (inc M⇒M') ,p inc (redex βT)
confluent▷⇒ {K = varKind -Term} βT (app (appl (app (appr ()))))
confluent▷⇒ {K = varKind -Term} (βT {A = A} {M} {N}) (app (appr (appl {E' = N'} N⇒N'))) = M ⟦ x₀:= N' ⟧ ,p (red-subr M (botsub-red N⇒N')) ,p (inc (redex βT))
confluent▷⇒ {K = varKind -Term} βT (app (appr (appr ())))
confluent▷⇒ {K = varKind -Path} cEE▷F (app cEE⇒G) with nfredexpath cEE▷F cEE⇒G
confluent▷⇒ {K = varKind -Path} cEE▷F (app cEE⇒G) | ()
confluent▷⇒ {K = nonVarKind _} () (app E⇒G)
\end{code}
}

\begin{cor}[Confluence]
\label{cor:confluence}
$ $
\begin{enumerate}
\item
The reduction relation is confluent: if $r \twoheadrightarrow s$ and $r \twoheadrightarrow s'$, then there exists $t$ such that $s \twoheadrightarrow t$ and $s' \twoheadrightarrow t$.

%<*Local-Confluent>
\begin{code}
local-confluent : ∀ {V} {C} {K} 
                  {E F G : Subexp V C K} → E ⇒ F → E ⇒ G → 
                  Σ[ H ∈ Subexp V C K ] (F ↠ H × G ↠ H)
\end{code}
%</local-confluent>

\AgdaHide{
\begin{code}
local-confluent (redex cEE▷F) cEE↠G = confluent▷⇒ cEE▷F cEE↠G
local-confluent cEE⇒F (redex cEE▷G) = let H ,p G↠H ,p F↠H = confluent▷⇒ cEE▷G cEE⇒F in 
  H ,p F↠H ,p G↠H
local-confluent (app {c = c} EE⇒FF) (app EE⇒GG) = let HH ,p FF↠HH ,p GG↠HH = local-confluent EE⇒FF EE⇒GG in 
  app c HH ,p app-red FF↠HH ,p app-red GG↠HH
local-confluent (appl E⇒F) (appl E⇒G) = let H ,p F↠H ,p G↠H = local-confluent E⇒F E⇒G in 
  _ ,p ∷-redl F↠H ,p ∷-redl G↠H
local-confluent (appl E⇒F) (appr EE⇒GG) = _ ,p inc (appr EE⇒GG) ,p inc (appl E⇒F)
local-confluent (appr EE⇒FF) (appl E⇒G) = _ ,p inc (appl E⇒G) ,p inc (appr EE⇒FF)
local-confluent (appr EE⇒FF) (appr EE⇒GG) = let HH ,p FF↠HH ,p GG↠HH = local-confluent EE⇒FF EE⇒GG in _ ,p ∷-redr FF↠HH ,p ∷-redr GG↠HH
\end{code}

\begin{code}
confluent : ∀ {V} {C} {K} 
                  {E F G : Subexp V C K} → E ↠ F → E ↠ G → 
                  Σ[ H ∈ Subexp V C K ] (F ↠ H × G ↠ H)
\end{code}

\AgdaHide{
\begin{code}
confluent (inc E⇒F) (inc E⇒G) = local-confluent E⇒F E⇒G
confluent {F = F} E↠F ref = F ,p ref ,p E↠F
confluent (inc E⇒F) (trans E↠G G↠G') = {!!}
confluent ref E↠G = {!!}
confluent (RTClose.trans E↠F E↠F₁) E↠G = {!!} -}
--TODO General theory of reduction
\end{code}
}

\item
If $r \simeq s$, then there exists $t$ such that $r \twoheadrightarrow t$ and $s \twoheadrightarrow t$.
--TODO Prove this
\end{enumerate}
\end{cor}

