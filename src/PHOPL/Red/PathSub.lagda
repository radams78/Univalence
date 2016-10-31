\AgdaHide{
\begin{code}
module PHOPL.Red.PathSub where
open import Data.Product
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Red.Base
\end{code}
}

\begin{lm}[Reduction respects substitution]
$ $
\begin{enumerate}
\item
If $t \rightarrow t'$ then $t[x:=s] \rightarrow t'[x:=s]$.
\item
If $t \rightarrow t'$ then $s[x:=t] \twoheadrightarrow s[x:=t']$.
\item
If $P \rightarrow P'$ then $M \{ x:= P : N \sim N' \} \twoheadrightarrow M \{ x:=P' : N \sim N' \}$.
\begin{code}
_↠p_ : ∀ {U V} → PathSub U V → PathSub U V → Set
τ ↠p τ' = ∀ x → τ x ↠ τ' x

postulate liftPathSub-red : ∀ {U V} {τ τ' : PathSub U V} → τ ↠p τ' → liftPathSub τ ↠p liftPathSub τ'

postulate red-pathsub : ∀ {U V} (M : Term U) {ρ σ : Sub U V} {τ τ' : PathSub U V} →
            τ ↠p τ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ↠ M ⟦⟦ τ' ∶ ρ ∼ σ ⟧⟧
{-red-pathsub (var x) τ↠pτ' = τ↠pτ' x
red-pathsub (app -bot []) τ↠pτ' = ref
red-pathsub (app -imp (φ ∷ ψ ∷ [])) τ↠pτ' = ⊃*-red (red-pathsub φ τ↠pτ') (red-pathsub ψ τ↠pτ')
red-pathsub (app (-lamTerm A) (M ∷ [])) τ↠pτ' = λλλ-red (red-pathsub M (liftPathSub-red τ↠pτ'))
red-pathsub (app -appTerm (M ∷ N ∷ [])) τ↠pτ' = app*-red ref ref (red-pathsub M τ↠pτ') (red-pathsub N τ↠pτ')-}

postulate red-pathsub-endl : ∀ {U V} (M : Term U) {ρ ρ' σ : Sub U V} {τ : PathSub U V} →
                      ρ ↠s ρ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ↠ M ⟦⟦ τ ∶ ρ' ∼ σ ⟧⟧

postulate red-pathsub-endr : ∀ {U V} (M : Term U) {ρ σ σ' : Sub U V} {τ : PathSub U V} →
                      σ ↠s σ' → M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ↠ M ⟦⟦ τ ∶ ρ ∼ σ' ⟧⟧
\end{code}
\end{enumerate}
\end{lm}

\begin{proof}
A straightforward induction in each case.
\end{proof}

\paragraph{Note}
It is not true in general that path substitution respects reduction; that is, that if $M \rightarrow M'$ then $M \{ x:=P : N \sim N' \} \twoheadrightarrow M' \{ x:=P : N \sim N' \}$.  For example, we have
$(\lambda x:\Omega.x)(\bot \supset \bot) \rightarrow \bot \supset \bot$,
but
\begin{align*}
(\bot \supset \bot) \{ \} & \equiv \reff{\bot} \supset^* \reff{\bot} \\
((\lambda x:\Omega.x)(\bot \supset \bot)) \{ \} & \equiv (\triplelambda e:x =_\Omega x'.e)(\reff{\bot} \supset^* \reff{\bot})
\end{align*}
The second of these paths does \emph{not} reduce to the first, because $\reff{\bot} \supset^* \reff{\bot}$ is not a normal form.

