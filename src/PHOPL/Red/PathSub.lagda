\AgdaHide{
\begin{code}
module PHOPL.Red.PathSub where
open import Data.Product
open import Prelims
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

\AgdaHide{
\begin{code}
postulate SNE : ∀ {V} {C} {K} (P : Subexp V C K → Set) →
              (∀ {M : Subexp V C K} → SN M → (∀ N → M ↠⁺ N → P N) → P M) →
              ∀ {M : Subexp V C K} → SN M → P M

private postulate var-red' : ∀ {V} {K} {x : Var V K} {M} {N} → M ↠ N → M ≡ var x → N ≡ var x
{-var-red' (inc (redex _)) ()
var-red' (inc (app _)) ()
var-red' ref M≡x = M≡x
var-red' (trans M↠N N↠P) M≡x = var-red' N↠P (var-red' M↠N M≡x) -}

postulate var-red : ∀ {V} {K} {x : Var V K} {M} → var x ↠ M → M ≡ var x
--var-red x↠M = var-red' x↠M refl

private postulate bot-red' : ∀ {V} {φ ψ : Term V} → φ ↠ ψ → φ ≡ ⊥ → ψ ≡ ⊥
{- bot-red' (inc (redex βT)) ()
bot-red' (inc (app {c = -bot} {F = []} x)) _ = refl
bot-red' (inc (app {c = -imp} _)) ()
bot-red' (inc (app {c = -appTerm} _)) ()
bot-red' (inc (app {c = -lamTerm _} _)) ()
bot-red' ref φ≡⊥ = φ≡⊥
bot-red' (trans φ↠ψ ψ↠χ) φ≡⊥ = bot-red' ψ↠χ (bot-red' φ↠ψ φ≡⊥) -}

postulate bot-red : ∀ {V} {φ : Term V} → ⊥ ↠ φ → φ ≡ ⊥
--bot-red ⊥↠φ = bot-red' ⊥↠φ refl

postulate imp-red' : ∀ {V} {φ ψ χ θ : Term V} → φ ↠ ψ → φ ≡ χ ⊃ θ →
                   Σ[ χ' ∈ Term V ] Σ[ θ' ∈ Term V ] χ ↠ χ' × θ ↠ θ' × ψ ≡ χ' ⊃ θ'
{-imp-red' (inc (redex βT)) ()
imp-red' (inc (app {c = -bot} _)) ()
imp-red' {θ = θ} (inc (app {c = -imp} (appl {E' = χ'} {F = _ ∷ []} χ⇒χ'))) φ≡χ⊃θ = 
  χ' ,p θ ,p subst (λ x → x ↠ χ') (imp-injl φ≡χ⊃θ) (inc χ⇒χ') ,p 
  ref ,p (cong (λ x → χ' ⊃ x) (imp-injr φ≡χ⊃θ))
imp-red' {χ = χ} (inc (app {c = -imp} (appr (appl {E' = θ'} {F = []} θ⇒θ')))) φ≡χ⊃θ = 
  χ ,p θ' ,p ref ,p (subst (λ x → x ↠ θ') (imp-injr φ≡χ⊃θ) (inc θ⇒θ')) ,p 
  cong (λ x → x ⊃ θ') (imp-injl φ≡χ⊃θ)
imp-red' (inc (app {c = -imp} (appr (appr ())))) _
imp-red' (inc (app {c = -appTerm} _)) ()
imp-red' (inc (app {c = -lamTerm _} _)) ()
imp-red' {χ = χ} {θ} ref φ≡χ⊃θ = χ ,p θ ,p ref ,p ref ,p φ≡χ⊃θ
imp-red' (trans φ↠ψ ψ↠ψ') φ≡χ⊃θ = 
  let (χ' ,p θ' ,p χ↠χ' ,p θ↠θ' ,p ψ≡χ'⊃θ') = imp-red' φ↠ψ φ≡χ⊃θ in 
  let (χ'' ,p θ'' ,p χ'↠χ'' ,p θ'↠θ'' ,p ψ'≡χ''⊃θ'') = imp-red' ψ↠ψ' ψ≡χ'⊃θ' in 
  χ'' ,p θ'' ,p RTClose.trans χ↠χ' χ'↠χ'' ,p RTClose.trans θ↠θ' θ'↠θ'' ,p ψ'≡χ''⊃θ''-}

postulate imp-red : ∀ {V} {χ θ ψ : Term V} → χ ⊃ θ ↠ ψ →
                  Σ[ χ' ∈ Term V ] Σ[ θ' ∈ Term V ] χ ↠ χ' × θ ↠ θ' × ψ ≡ χ' ⊃ θ'
--imp-red χ⊃θ↠ψ = imp-red' χ⊃θ↠ψ refl

postulate conv-rep : ∀ {U} {V} {C} {K} {ρ : Rep U V} {M N : Subexp U C K} → M ≃ N → M 〈 ρ 〉 ≃ N 〈 ρ 〉

postulate conv-sub : ∀ {U} {V} {C} {K} {σ : Sub U V} {M N : Subexp U C K} → M ≃ N → M ⟦ σ ⟧ ≃ N ⟦ σ ⟧

postulate appT-convl : ∀ {V} {M M' N : Term V} → M ≃ M' → appT M N ≃ appT M' N

data redVT {V} : ∀ {n} → snocVec (Term V) n → snocVec (Term V) n → Set where
  redleft : ∀ {n} {MM MM' : snocVec (Term V) n} {N} → redVT MM MM' → redVT (MM snoc N) (MM' snoc N)
  redright : ∀ {n} {MM : snocVec (Term V) n} {N N'} → N ⇒ N' → redVT (MM snoc N) (MM snoc N')

data redVP {V} : ∀ {n} → snocVec (Proof V) n → snocVec (Proof V) n → Set where
  redleft : ∀ {n} {εε εε' : snocVec _ n} {δ} → redVP εε εε' → redVP (εε snoc δ) (εε' snoc δ)
  redright : ∀ {n} {εε : snocVec _ n} {δ} {δ'} → δ ⇒ δ' → redVP (εε snoc δ) (εε snoc δ')

data redVPa {V} : ∀ {n} → snocVec (Path V) n → snocVec (Path V) n → Set where
  redleft : ∀ {n} {PP PP' : snocVec (Path V) n} {Q} → redVPa PP PP' → redVPa (PP snoc Q) (PP' snoc Q)
  redright : ∀ {n} {PP : snocVec (Path V) n} {Q Q'} → Q ⇒ Q' → redVPa (PP snoc Q) (PP snoc Q')

postulate APPP-redl : ∀ {V n δ δ'} {εε : snocVec (Proof V) n} → δ ⇒ δ' → APPP δ εε ⇒ APPP δ' εε
{-APPP-redl {εε = []} δ⇒δ' = δ⇒δ'
APPP-redl {εε = εε snoc _} δ⇒δ' = app (appl (APPP-redl {εε = εε} δ⇒δ'))-}

postulate APP*-red₁ : ∀ {V n} {MM MM' NN : snocVec (Term V) n} {P PP} → redVT MM MM' → APP* MM NN P PP ⇒ APP* MM' NN P PP
--APP*-red₁ {NN = _ snoc _} {PP = _ snoc _} (redleft MM⇒MM') = app (appr (appr (appl (APP*-red₁ MM⇒MM'))))
--APP*-red₁ {NN = _ snoc _} {PP = _ snoc _} (redright M⇒M') = app (appl M⇒M')

postulate APP*-red₂ : ∀ {V n} MM {NN NN' : snocVec (Term V) n} {P PP} → redVT NN NN' → APP* MM NN P PP ⇒ APP* MM NN' P PP
--APP*-red₂ (MM snoc _) {_ snoc _} {_ snoc _} {PP = _ snoc _} (redleft NN⇒NN') = app (appr (appr (appl (APP*-red₂ MM NN⇒NN'))))
--APP*-red₂ (_ snoc _) {PP = _ snoc _} (redright N⇒N') = app (appr (appl N⇒N'))

postulate APP*-red₃ : ∀ {V n} MM {NN : snocVec (Term V) n} {P P' PP} → P ⇒ P' → APP* MM NN P PP ⇒ APP* MM NN P' PP
--APP*-red₃ [] {[]} {PP = []} P⇒P' = P⇒P'
--APP*-red₃ (MM snoc M) {NN snoc N} {PP = PP snoc P} P⇒P' = app (appr (appr (appl (APP*-red₃ MM P⇒P'))))
\end{code}
