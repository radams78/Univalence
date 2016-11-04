\AgdaHide{
\begin{code}
module PHOPL.KeyRedex2.SNE where
open import Data.Nat
open import Prelims
open import Prelims.Closure
open import PHOPL.Grammar
open import PHOPL.Red
\end{code}
}

\begin{proposition}
\label{prop:SNE}
If $(P[x:=L, y:=L', e:=Q]_{M_1 N_1} Q_1 \cdots_{M_n N_n} Q_n)^+ \delta_1 \cdots \delta_m \in \SN$ and $L, L', Q \in \SN$ then $((\triplelambda e:x =_A y.P)_{L L'} Q_{M_1 N_1} Q_1 \cdots_{M_n N_n} Q_n)^+ \delta_1 \cdots \delta_m \in \SN$.
\end{proposition}

\AgdaHide{
\begin{code}
pre-lmSNE₁ : ∀ {V} {L L' : Term V} {P Q A F} {C : Path V → Set} →
                     C (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) →
                     (∀ L₁ → L ⇒ L₁ → C (app* L₁ L' (λλλ A P) Q)) →
                     (∀ L'₁ → L' ⇒ L'₁ → C (app* L L'₁ (λλλ A P) Q)) →
                     (∀ P₁ → P ⇒ P₁ → C (app* L L' (λλλ A P₁) Q)) →
                     (∀ Q₁ → Q ⇒ Q₁ → C (app* L L' (λλλ A P) Q₁)) →
                     app* L L' (λλλ A P) Q ⇒ F → C F
pre-lmSNE₁ hyp-red _ _ _ _ (redex (βR ()))
pre-lmSNE₁ hyp-red _ _ _ _ (redex (R₀R (βE _ _ _ _))) = hyp-red
pre-lmSNE₁ _ hypL _ _ _ (app (appl L⇒L')) = hypL _ L⇒L'
pre-lmSNE₁ _ _ hypL' _ _ (app (appr (appl L₁⇒L'₁))) = hypL' _ L₁⇒L'₁
pre-lmSNE₁ _ _ _ _ _ (app (appr (appr (appl (redex (βR ()))))))
pre-lmSNE₁ _ _ _ _ _ (app (appr (appr (appl (redex (R₀R ()))))))
pre-lmSNE₁ _ _ _ hypP _ (app (appr (appr (appl (app (appl P⇒P')))))) = hypP _ P⇒P'
pre-lmSNE₁ _ _ _ _ _ (app (appr (appr (appl (app (appr ()))))))
pre-lmSNE₁ _ _ _ _ hypQ (app (appr (appr (appr (appl Q⇒Q'))))) = hypQ _ Q⇒Q'
pre-lmSNE₁ _ _ _ _ _ (app (appr (appr (appr (appr ())))))

pre-lmSNE₂ : ∀ {n} {V} {L L' : Term V} {P Q A F} {MM NN : snocVec (Term V) n} {PP} 
                     {C : Path V → Set} →
                     C (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) PP) →
                     (∀ MM' → redVT MM MM' → C (APP* MM' NN (app* L L' (λλλ A P) Q) PP)) →
                     (∀ NN' → redVT NN NN' → C (APP* MM NN' (app* L L' (λλλ A P) Q) PP)) →
                     (∀ L₁ → L ⇒ L₁ → C (APP* MM NN (app* L₁ L' (λλλ A P) Q) PP)) →
                     (∀ L'₁ → L' ⇒ L'₁ → C (APP* MM NN (app* L L'₁ (λλλ A P) Q) PP)) →
                     (∀ P₁ → P ⇒ P₁ → C (APP* MM NN (app* L L' (λλλ A P₁) Q) PP)) →
                     (∀ Q₁ → Q ⇒ Q₁ → C (APP* MM NN (app* L L' (λλλ A P) Q₁) PP)) →
                     (∀ PP' → osrVPa PP PP' → C (APP* MM NN (app* L L' (λλλ A P) Q) PP')) →
                     APP* MM NN (app* L L' (λλλ A P) Q) PP ⇒ F → C F
pre-lmSNE₂ {MM = []} {[]} {[]} hyp-red _ _ hypL hypL' hypP hypQ _ PQPP⇒F = pre-lmSNE₁ hyp-red hypL hypL' hypP hypQ PQPP⇒F
pre-lmSNE₂ {MM = [] snoc _} {[] snoc _} {[] snoc _} _ _ _ _ _ _ _ _ (redex (R₀R ()))
pre-lmSNE₂ {MM = [] snoc _} {[] snoc _} {[] snoc _} _ _ _ _ _ _ _ _ (redex (βR ()))
pre-lmSNE₂ {MM = _ snoc _} {_ snoc _} {_ snoc _} _ hypMM _ _ _ _ _ _ (app (appl M⇒M')) = hypMM _ (redright M⇒M')
pre-lmSNE₂ {MM = _ snoc _} {_ snoc _} {_ snoc _} _ _ hypNN _ _ _ _ _ (app (appr (appl N⇒N'))) = hypNN _ (redright N⇒N')
pre-lmSNE₂ {MM = _ snoc _} {_ snoc _} {_ snoc P} _ _ _ _ _ _ _ hypPP (app (appr (appr (appr (appl P⇒P'))))) = hypPP _ (redright P⇒P')
pre-lmSNE₂ {MM = _ snoc _} {_ snoc _} {_ snoc _} _ _ _ _ _ _ _ _ (app (appr (appr (appr (appr ())))))
pre-lmSNE₂ {MM = _ snoc _ snoc _} {_ snoc _ snoc _} {_ snoc _ snoc _} _ _ _ _ _ _ _ _ (redex (βR ()))
pre-lmSNE₂ {MM = _ snoc _ snoc _} {_ snoc _ snoc _} {_ snoc _ snoc _} _ _ _ _ _ _ _ _ (redex (R₀R ()))
pre-lmSNE₂ {MM = MM snoc M} {NN snoc N} {PP snoc P} {C = C} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP (app (appr (appr (appl PQPP⇒F)))) = 
  pre-lmSNE₂ {MM = MM} {NN} {PP} {C = λ x → C (app* M N x P)} 
    hyp-red 
    (λ _ MM⇒MM' → hypMM _ (redleft MM⇒MM')) (λ _ NN⇒NN' → hypNN _ (redleft NN⇒NN'))
    hypL hypL' hypP hypQ 
    (λ _ PP⇒PP' → hypPP _ (redleft PP⇒PP')) 
    PQPP⇒F

pre-lmSNE₃ : ∀ {n} {V} {L L' : Term V} {P Q A F} {MM NN : snocVec (Term V) n} {PP} {C : Proof V → Set} →
                     C (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) PP)) →
                     (∀ MM' → redVT MM MM' → C (plus (APP* MM' NN (app* L L' (λλλ A P) Q) PP))) →
                     (∀ NN' → redVT NN NN' → C (plus (APP* MM NN' (app* L L' (λλλ A P) Q) PP))) →
                     (∀ L₁ → L ⇒ L₁ → C (plus (APP* MM NN (app* L₁ L' (λλλ A P) Q) PP))) →
                     (∀ L'₁ → L' ⇒ L'₁ → C (plus (APP* MM NN (app* L L'₁ (λλλ A P) Q) PP))) →
                     (∀ P₁ → P ⇒ P₁ → C (plus (APP* MM NN (app* L L' (λλλ A P₁) Q) PP))) →
                     (∀ Q₁ → Q ⇒ Q₁ → C (plus (APP* MM NN (app* L L' (λλλ A P) Q₁) PP))) →
                     (∀ PP' → osrVPa PP PP' → C (plus (APP* MM NN (app* L L' (λλλ A P) Q) PP'))) →
                     plus (APP* MM NN (app* L L' (λλλ A P) Q) PP) ⇒ F → C F
pre-lmSNE₃ {MM = []} {[]} {[]} _ _ _ _ _ _ _ _ (redex (βR ()))
pre-lmSNE₃ {MM = []} {[]} {[]} _ _ _ _ _ _ _ _ (redex (R₀R ()))
pre-lmSNE₃ {MM = _ snoc _} {_ snoc _} {_ snoc _} _ _ _ _ _ _ _ _ (redex (βR ()))
pre-lmSNE₃ {MM = _ snoc _} {_ snoc _} {_ snoc _} _ _ _ _ _ _ _ _ (redex (R₀R ()))
pre-lmSNE₃ {C = C} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP (app (appl plusPQPP⇒F)) = 
  pre-lmSNE₂ {C = λ x → C (plus x)} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP plusPQPP⇒F
pre-lmSNE₃ hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP (app (appr ()))

pre-lmSNE₄ : ∀ {m n V} {L L' : Term V} {P Q A F} {MM NN : snocVec (Term V) n} {PP} {δδ : snocVec (Proof V) m} {C : Proof V → Set} →
                     C (APPP (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) PP)) δδ) →
                     (∀ MM' → redVT MM MM' → C (APPP (plus (APP* MM' NN (app* L L' (λλλ A P) Q) PP)) δδ)) →
                     (∀ NN' → redVT NN NN' → C (APPP (plus (APP* MM NN' (app* L L' (λλλ A P) Q) PP)) δδ)) →
                     (∀ L₁ → L ⇒ L₁ → C (APPP (plus (APP* MM NN (app* L₁ L' (λλλ A P) Q) PP)) δδ)) →
                     (∀ L'₁ → L' ⇒ L'₁ → C (APPP (plus (APP* MM NN (app* L L'₁ (λλλ A P) Q) PP)) δδ)) →
                     (∀ P₁ → P ⇒ P₁ → C (APPP (plus (APP* MM NN (app* L L' (λλλ A P₁) Q) PP)) δδ)) →
                     (∀ Q₁ → Q ⇒ Q₁ → C (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q₁) PP)) δδ)) →
                     (∀ PP' → osrVPa PP PP' → C (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) PP')) δδ)) →
                     (∀ δδ' → osrVP δδ δδ' → C (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) PP)) δδ')) →
                     APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) PP)) δδ ⇒ F → C F
pre-lmSNE₄ {δδ = []} {C = C} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP _ plusPQPP⇒F = pre-lmSNE₃ {C = C} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP plusPQPP⇒F
pre-lmSNE₄ {δδ = [] snoc _} _ _ _ _ _ _ _ _ _ (redex (βR ()))
pre-lmSNE₄ {δδ = [] snoc _} _ _ _ _ _ _ _ _ _ (redex (R₀R ()))
pre-lmSNE₄ {δδ = _ snoc _ snoc _} _ _ _ _ _ _ _ _ _ (redex (βR ()))
pre-lmSNE₄ {δδ = _ snoc _ snoc _} _ _ _ _ _ _ _ _ _ (redex (R₀R ()))
pre-lmSNE₄ {δδ = δδ snoc δ} {C = C} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP hypδδ (app (appl plusPQPPδδ⇒F)) = 
  pre-lmSNE₄ {δδ = δδ} {C = λ x → C (appP x δ)} hyp-red hypMM hypNN hypL hypL' hypP hypQ hypPP 
  (λ _ δδ⇒δδ' → hypδδ _ (redleft δδ⇒δδ')) plusPQPPδδ⇒F
pre-lmSNE₄ {δδ = _ snoc _} _ _ _ _ _ _ _ _ hypδδ (app (appr (appl δ⇒δ'))) = hypδδ _ (redright δ⇒δ')
pre-lmSNE₄ {δδ = _ snoc _} _ _ _ _ _ _ _ _ _ (app (appr (appr ())))

lmSNE : ∀ {m n V} {L L' : Term V} {P Q A} MM {NN : snocVec (Term V) n} {PP} (δδ : snocVec (Proof V) m) →
                SN (APPP (plus (APP* MM NN (P ⟦ x₂:= L ,x₁:= L' ,x₀:= Q ⟧) PP)) δδ) → SN L → SN L' → SN Q →
                SN (APPP (plus (APP* MM NN (app* L L' (λλλ A P) Q) PP)) δδ)
lmSNE {L = L} {L'} {P} {Q} {A} MM {NN} {PP} δδ (SNI _ SNPPPδδ) (SNI _ SNL) (SNI _ SNL') (SNI _ SNQ) = SNI _ (λ F plusPQPPδδ⇒F →
  pre-lmSNE₄ {L = L} {L'} {P} {Q} {A} {F} {MM} {NN} {PP} {δδ} {C = SN} (SNI _ SNPPPδδ) 
  (λ MM' MM⇒MM' → lmSNE MM' δδ (SNPPPδδ _ (APPP-osrl (app (appl (APP*-osr₁ MM⇒MM'))) δδ)) (SNI _ SNL) (SNI _ SNL') (SNI _ SNQ)) 
  (λ NN' NN⇒NN' → lmSNE MM δδ (SNPPPδδ _ (APPP-osrl (app (appl (APP*-osr₂ MM NN⇒NN'))) δδ)) (SNI _ SNL) (SNI _ SNL') (SNI _ SNQ)) 
  (λ L₁ L⇒L₁ → lmSNE MM δδ (SNred (SNI _ SNPPPδδ) (APPP-redl (plus-red (APP*-red₃ MM (red-subr P (botsub₃-red (inc L⇒L₁) ref ref)))) δδ)) (SNL _ L⇒L₁) (SNI _ SNL') (SNI _ SNQ))
  (λ L'₁ L'⇒L'₁ → lmSNE MM δδ (SNred (SNI _ SNPPPδδ) (APPP-redl (plus-red (APP*-red₃ MM (red-subr P (botsub₃-red ref (inc L'⇒L'₁) ref)))) δδ)) (SNI _ SNL) (SNL' _ L'⇒L'₁) (SNI _ SNQ)) 
  (λ P' P⇒P' → lmSNE MM δδ (SNPPPδδ _ (APPP-osrl (app (appl (APP*-osr₃ MM (osr-subl P⇒P')))) δδ)) (SNI _ SNL) (SNI _ SNL') (SNI _ SNQ)) 
  (λ Q' Q⇒Q' → lmSNE MM δδ (SNred (SNI _ SNPPPδδ) (APPP-redl (plus-red (APP*-red₃ MM (red-subr P (botsub₃-red ref ref (inc Q⇒Q'))))) δδ)) (SNI _ SNL) (SNI _ SNL') (SNQ _ Q⇒Q')) 
  (λ PP' PP⇒PP' → lmSNE MM δδ (SNPPPδδ _ (APPP-osrl (app (appl (APP*-osr₄ MM PP⇒PP'))) δδ)) (SNI _ SNL) (SNI _ SNL') (SNI _ SNQ)) 
  (λ δδ' δδ⇒δδ' → lmSNE MM δδ' (SNPPPδδ _ (APPP-osrr δδ⇒δδ')) (SNI _ SNL) (SNI _ SNL') (SNI _ SNQ)) 
  plusPQPPδδ⇒F)
\end{code}
}
