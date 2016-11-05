\AgdaHide{
\begin{code}
module PHOPL.Computable.NFProof where
open import Data.Product
open import Prelims
open import PHOPL.Grammar
open import PHOPL.Neutral
open import PHOPL.Red
\end{code}
}

Note first that (using Generation) a normal form of type $\Omega$ is either $\bot$, or a neutral term, or $\phi \supset \psi$ where $\phi$ and $\psi$ are normal forms of type $\Omega$.

\AgdaHide{
\begin{code}
data Shape : Set where
  neutral : Shape
  bot : Shape
  imp : Shape → Shape → Shape

data Leaves (V : Alphabet) : Shape → Set where
  neutral : Neutral V → Leaves V neutral
  bot : Leaves V bot
  imp : ∀ {S} {T} → Leaves V S → Leaves V T → Leaves V (imp S T)

lrep : ∀ {U} {V} {S} → Leaves U S → Rep U V → Leaves V S
lrep (neutral N) ρ = neutral (nrep N ρ)
lrep bot _ = bot
lrep (imp φ ψ) ρ = imp (lrep φ ρ) (lrep ψ ρ)

nrep-id : ∀ {V} {N : Neutral V} → nrep N (idRep V) ≡ N
nrep-id {N = var _} = refl
nrep-id {N = app N M} = cong₂ app nrep-id rep-idRep

lrep-id : ∀ {V} {S} {L : Leaves V S} → lrep L (idRep V) ≡ L
lrep-id {L = neutral x} = cong neutral nrep-id
lrep-id {L = bot} = refl
lrep-id {L = imp L L'} = cong₂ imp lrep-id lrep-id

postulate lrep-comp : ∀ {U V W S} {ρ' : Rep V W} {ρ} {L : Leaves U S} →
                    lrep L (ρ' •R ρ) ≡ lrep (lrep L ρ) ρ'
{- lrep-comp {L = neutral _} = cong neutral nrep-comp
lrep-comp {L = bot} = refl
lrep-comp {L = imp φ ψ} = cong₂ imp lrep-comp lrep-comp -}

decode-Prop : ∀ {V} {S} → Leaves V S → Term V
decode-Prop (neutral N) = decode-Neutral N
decode-Prop bot = ⊥
decode-Prop (imp φ ψ) = decode-Prop φ ⊃ decode-Prop ψ

postulate decode-rep : ∀ {U} {V} {S} (L : Leaves U S) {ρ : Rep U V} →
                     decode-Prop (lrep L ρ) ≡ decode-Prop L 〈 ρ 〉

postulate leaves-red : ∀ {V} {S} {L : Leaves V S} {φ : Term V} →
                     decode-Prop L ↠ φ →
                     Σ[ L' ∈ Leaves V S ] decode-Prop L' ≡ φ
{- leaves-red {S = neutral} {L = neutral N} L↠φ = 
  let (N ,p N≡φ) = neutral-red {N = N} L↠φ in neutral N ,p N≡φ
leaves-red {S = bot} {L = bot} L↠φ = bot ,p Prelims.sym (bot-red L↠φ)
leaves-red {S = imp S T} {L = imp φ ψ} φ⊃ψ↠χ = 
  let (φ' ,p ψ' ,p φ↠φ' ,p ψ↠ψ' ,p χ≡φ'⊃ψ') = imp-red φ⊃ψ↠χ in 
  let (L₁ ,p L₁≡φ') = leaves-red {L = φ} φ↠φ' in 
  let (L₂ ,p L₂≡ψ') = leaves-red {L = ψ} ψ↠ψ' in 
  (imp L₁ L₂) ,p (Prelims.trans (cong₂ _⊃_ L₁≡φ' L₂≡ψ') (Prelims.sym χ≡φ'⊃ψ')) -}

postulate red-decode-rep : ∀ {U} {V} {φ : Term U} {S} (L : Leaves U S) {ρ : Rep U V} →
                         φ ↠ decode-Prop L → φ 〈 ρ 〉 ↠ decode-Prop (lrep L ρ)
{- red-decode-rep {V = V} {φ} L {ρ} φ↠L = let open Relation.Binary.PreorderReasoning (RED V -Expression (varKind -Term)) in 
  begin
    φ 〈 ρ 〉
  ∼⟨ red-rep φ↠L ⟩
    decode-Prop L 〈 ρ 〉
  ≈⟨ Prelims.sym (decode-rep L) ⟩
    decode-Prop (lrep L ρ)
  ∎ -}
\end{code}
}

