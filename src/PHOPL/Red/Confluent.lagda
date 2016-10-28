\AgdaHide{
\begin{code}
module PHOPL.Red.Confluent where
open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red

pre-confluent : ∀ {V} {K} {C} {c : Con (SK C K)} {EE : ListAbs V C} {F G} →
                R c EE F → app c EE ⇒ G → Σ[ H ∈ Expression V K ] F ↠ H × G ↠ H
pre-confluent {F = F} cEE▷F (redex E▷G) = F ,p ref ,p (subst (λ x → x ↠ F) (R-det cEE▷F E▷G) ref)
pre-confluent {K = varKind -Proof} cEE▷F (app cEE⇒G) with nfredexproof cEE▷F cEE⇒G
pre-confluent {K = varKind -Proof} cEE▷F (app cEE⇒G) | ()
pre-confluent {K = varKind -Term} βT (app (appl (redex ())))
pre-confluent {K = varKind -Term} (βT {N = N}) (app (appl (app (appl {E' = M'} M⇒M')))) = M' ⟦ x₀:= N ⟧ ,p red-subl (inc M⇒M') ,p inc (redex βT)
pre-confluent {K = varKind -Term} βT (app (appl (app (appr ()))))
pre-confluent {K = varKind -Term} (βT {A = A} {M} {N}) (app (appr (appl {E' = N'} N⇒N'))) = M ⟦ x₀:= N' ⟧ ,p (red-subr M (botsub-red N⇒N')) ,p (inc (redex βT))
pre-confluent {K = varKind -Term} βT (app (appr (appr ())))
pre-confluent {K = varKind -Path} cEE▷F (app cEE⇒G) with nfredexpath cEE▷F cEE⇒G
pre-confluent {K = varKind -Path} cEE▷F (app cEE⇒G) | ()
pre-confluent {K = nonVarKind _} () (app E⇒G)
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
local-confluent (redex cEE▷F) cEE↠G = pre-confluent cEE▷F cEE↠G
local-confluent cEE⇒F (redex cEE▷G) = let H ,p G↠H ,p F↠H = pre-confluent cEE▷G cEE⇒F in 
  H ,p F↠H ,p G↠H
local-confluent (app {c = c} EE⇒FF) (app EE⇒GG) = let HH ,p FF↠HH ,p GG↠HH = local-confluent EE⇒FF EE⇒GG in 
  app c HH ,p app-red FF↠HH ,p app-red GG↠HH
local-confluent (appl E⇒F) (appl E⇒G) = let H ,p F↠H ,p G↠H = local-confluent E⇒F E⇒G in 
  _ ,p ∷-redl F↠H ,p ∷-redl G↠H
local-confluent (appl E⇒F) (appr EE⇒GG) = _ ,p inc (appr EE⇒GG) ,p inc (appl E⇒F)
local-confluent (appr EE⇒FF) (appl E⇒G) = _ ,p inc (appl E⇒G) ,p inc (appr EE⇒FF)
local-confluent (appr EE⇒FF) (appr EE⇒GG) = let HH ,p FF↠HH ,p GG↠HH = local-confluent EE⇒FF EE⇒GG in _ ,p ∷-redr FF↠HH ,p ∷-redr GG↠HH
--TODO General theory of reduction
\end{code}
}

\item
If $r \simeq s$, then there exists $t$ such that $r \twoheadrightarrow t$ and $s \twoheadrightarrow t$.
--TODO Prove this
\end{enumerate}
\end{cor}

